import SRBodyCovariancePositive
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! SR 5.7: actual linear comparisons preserving the full body preserve its
Lebesgue measure and its covariance; the covariance inverse form is invariant.
No determinant, volume-preservation or invariant-inner-product certificate is
an input. There is no compactness assumption on the comparison group. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Set Filter
open scoped Matrix BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def srRestMatrix (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : Matrix ι ι ℝ:=
  LinearMap.toMatrix' h.toLinearMap

theorem sr_body_has_positive_finite_volume (K : Set (ι → ℝ))
    (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:ι → ℝ)) :
    0<volume K ∧ volume K<⊤ := by
  have hi:(interior K).Nonempty:=⟨0,mem_interior_iff_mem_nhds.mpr zeroInterior⟩
  exact ⟨lt_of_lt_of_le (isOpen_interior.measure_pos volume hi)
    (measure_mono interior_subset),compact.measure_lt_top⟩

theorem sr_body_comparison_abs_det_one (K : Set (ι → ℝ)) (compact : IsCompact K)
    (zeroInterior : K∈𝓝 (0:ι → ℝ)) (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (preserves : h '' K=K) : |LinearMap.det h.toLinearMap|=1 := by
  obtain ⟨hp,hf⟩:=sr_body_has_positive_finite_volume K compact zeroInterior
  have hreal:0<(volume K).toReal:=ENNReal.toReal_pos hp.ne' hf.ne
  have he:=congrArg ENNReal.toReal (volume.addHaar_image_continuousLinearEquiv h K)
  rw [preserves] at he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)] at he
  change (volume K).toReal=|LinearMap.det h.toLinearMap| * (volume K).toReal at he
  nlinarith

theorem sr_body_comparison_preserves_lebesgue (K : Set (ι → ℝ)) (compact : IsCompact K)
    (zeroInterior : K∈𝓝 (0:ι → ℝ)) (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (preserves : h '' K=K) : MeasurePreserving h volume volume := by
  have hd:=sr_body_comparison_abs_det_one K compact zeroInterior h preserves
  have hn:LinearMap.det h.toLinearMap≠0:=(LinearEquiv.isUnit_det' h.toLinearEquiv).ne_zero
  refine ⟨h.continuous.measurable,?_⟩
  change Measure.map h.toLinearMap volume=volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hn]
  simp only [abs_inv,hd,inv_one,ENNReal.ofReal_one,one_smul]

theorem sr_covariance_bilinear_is_integral (K : Set (ι → ℝ)) (compact : IsCompact K)
    (z w : ι → ℝ) :
    z ⬝ᵥ srBodyCovariance K *ᵥ w=∫ y in K,(z ⬝ᵥ y)*(w ⬝ᵥ y) := by
  have hi (i j:ι):IntegrableOn (fun y:ι → ℝ=>z i*(y i*y j)*w j) K:=
    (by fun_prop : Continuous (fun y:ι → ℝ=>z i*(y i*y j)*w j)).continuousOn.integrableOn_compact compact
  have hs (i:ι):IntegrableOn (fun y:ι → ℝ=>∑ j,z i*(y i*y j)*w j) K:=
    (by fun_prop : Continuous (fun y:ι → ℝ=>∑ j,z i*(y i*y j)*w j)).continuousOn.integrableOn_compact compact
  symm
  calc
    _=∫ y in K,∑ i,∑ j,z i*(y i*y j)*w j := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      simp only [dotProduct,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=∑ i,∑ j,∫ y in K,z i*(y i*y j)*w j := by
      rw [integral_finset_sum Finset.univ (fun i _=>hs i)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finset_sum Finset.univ (fun j _=>hi i j)
    _=z ⬝ᵥ srBodyCovariance K *ᵥ w := by
      simp only [integral_mul_const,integral_const_mul,dotProduct,Matrix.mulVec,
        srBodyCovariance,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem sr_rest_matrix_applies (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    srRestMatrix h *ᵥ x=h x := LinearMap.toMatrix'_mulVec h.toLinearMap x

theorem sr_covariance_transforms_under_full_body_comparison
    (K : Set (ι → ℝ)) (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:ι → ℝ))
    (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (preserves : h '' K=K) :
    srRestMatrix h*srBodyCovariance K*(srRestMatrix h).transpose=srBodyCovariance K := by
  have hp:=sr_body_comparison_preserves_lebesgue K compact zeroInterior h preserves
  have hem:=h.toHomeomorph.isClosedEmbedding.measurableEmbedding
  ext i j
  rw [Matrix.mul_mul_apply,Matrix.transpose_transpose,sr_covariance_bilinear_is_integral K compact]
  have hc (x:ι → ℝ) (i:ι) : srRestMatrix h i ⬝ᵥ x=h x i:=
    congrFun (sr_rest_matrix_applies h x) i
  simp_rw [hc]
  have he:=hp.setIntegral_image_emb hem (fun y:ι → ℝ=>y i*y j) K
  rw [preserves] at he
  exact he.symm

theorem sr_rest_matrix_inverse_identities (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    srRestMatrix h*srRestMatrix h.symm=1 ∧ srRestMatrix h.symm*srRestMatrix h=1 := by
  have hr:h.toLinearMap.comp h.symm.toLinearMap=LinearMap.id:=by ext x;simp
  have hl:h.symm.toLinearMap.comp h.toLinearMap=LinearMap.id:=by ext x;simp
  constructor
  · simpa only [srRestMatrix,LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' hr
  · simpa only [srRestMatrix,LinearMap.toMatrix'_comp,LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' hl

theorem sr_covariance_inverse_congruence_invariant
    (K : Set (ι → ℝ)) (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:ι → ℝ))
    (h : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (preserves : h '' K=K) :
    (srRestMatrix h).transpose*(srBodyCovariance K)⁻¹*srRestMatrix h=(srBodyCovariance K)⁻¹ := by
  let A:=srRestMatrix h
  let B:=srRestMatrix h.symm
  have hab:A*B=1:=(sr_rest_matrix_inverse_identities h).1
  have hba:B*A=1:=(sr_rest_matrix_inverse_identities h).2
  have hai:A⁻¹=B:=Matrix.inv_eq_right_inv hab
  have hi:=congrArg (fun M:Matrix ι ι ℝ=>M⁻¹)
    (sr_covariance_transforms_under_full_body_comparison K compact zeroInterior h preserves)
  change (A*srBodyCovariance K*A.transpose)⁻¹=(srBodyCovariance K)⁻¹ at hi
  have hb:B.transpose*(srBodyCovariance K)⁻¹*B=(srBodyCovariance K)⁻¹:=by
    simpa only [Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv,hai,Matrix.mul_assoc] using hi
  have hm:=congrArg (fun M:Matrix ι ι ℝ=>A.transpose*M*A) hb
  have hleft:A.transpose*(B.transpose*(srBodyCovariance K)⁻¹*B)*A=(srBodyCovariance K)⁻¹:=by
    calc
      _=(B*A).transpose*(srBodyCovariance K)⁻¹*(B*A):=by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _=(srBodyCovariance K)⁻¹:=by simp only [hba,Matrix.transpose_one,one_mul,mul_one]
  exact hm.symm.trans hleft

#print axioms sr_body_has_positive_finite_volume
#print axioms sr_body_comparison_abs_det_one
#print axioms sr_body_comparison_preserves_lebesgue
#print axioms sr_covariance_bilinear_is_integral
#print axioms sr_rest_matrix_applies
#print axioms sr_covariance_transforms_under_full_body_comparison
#print axioms sr_rest_matrix_inverse_identities
#print axioms sr_covariance_inverse_congruence_invariant
end
end AASCMetricConstruction
