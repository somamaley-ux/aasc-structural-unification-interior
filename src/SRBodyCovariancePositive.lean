import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! SR 5.7: construct the second-moment covariance from the full body,
and prove it positive definite using its actual interior. Coordinates and
Lebesgue measure are auxiliary. No quadratic body or spatial form is input.
The unnormalized covariance differs by a positive volume factor; boundary
normalization removes that factor in the final unit-ball form. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Set Filter
open scoped Matrix BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def srBodyCovariance (K : Set (ι → ℝ)) : Matrix ι ι ℝ:=
  fun i j=>∫ y in K,y i*y j

theorem sr_covariance_is_hermitian (K : Set (ι → ℝ)) :
    (srBodyCovariance K).IsHermitian := by
  ext i j
  simp [srBodyCovariance,Matrix.conjTranspose_apply,mul_comm]

theorem sr_covariance_quadratic_is_integral (K : Set (ι → ℝ)) (compact : IsCompact K)
    (z : ι → ℝ) :
    z ⬝ᵥ srBodyCovariance K *ᵥ z=∫ y in K,(z ⬝ᵥ y)^2 := by
  have hi (i j:ι):IntegrableOn (fun y:ι → ℝ=>z i*(y i*y j)*z j) K:=
    (by fun_prop : Continuous (fun y:ι → ℝ=>z i*(y i*y j)*z j)).continuousOn.integrableOn_compact compact
  have hs (i:ι):IntegrableOn (fun y:ι → ℝ=>∑ j,z i*(y i*y j)*z j) K:=
    (by fun_prop : Continuous (fun y:ι → ℝ=>∑ j,z i*(y i*y j)*z j)).continuousOn.integrableOn_compact compact
  symm
  calc
    _=∫ y in K,∑ i,∑ j,z i*(y i*y j)*z j := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      simp only [dotProduct,pow_two,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=∑ i,∑ j,∫ y in K,z i*(y i*y j)*z j := by
      rw [integral_finset_sum Finset.univ (fun i _=>hs i)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finset_sum Finset.univ (fun j _=>hi i j)
    _=z ⬝ᵥ srBodyCovariance K *ᵥ z := by
      simp only [integral_mul_const,integral_const_mul,dotProduct,Matrix.mulVec,
        srBodyCovariance,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem sr_nonzero_linear_query_has_occupied_interior_answer
    (K : Set (ι → ℝ)) (zeroInterior : K∈𝓝 (0:ι → ℝ))
    (z : ι → ℝ) (nonzero : z≠0) :
    ∃ y∈interior K,z ⬝ᵥ y≠0 := by
  have hex:∃ i,z i≠0:=by
    by_contra hn
    push_neg at hn
    exact nonzero (funext hn)
  obtain ⟨i,hi⟩:=hex
  let v:ι → ℝ:=Pi.single i 1
  let U:Set ℝ:=(fun t:ℝ=>t • v) ⁻¹' interior K
  have hU:IsOpen U:=isOpen_interior.preimage (continuous_id.smul continuous_const)
  have hz:(0:ℝ)∈U:=by
    simpa [U] using (mem_interior_iff_mem_nhds.mpr zeroInterior)
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hU 0 hz
  have ht:r/2∈U:=by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by linarith : 0<r/2)]
    linarith
  refine ⟨(r/2) • v,ht,?_⟩
  have he:z ⬝ᵥ ((r/2) • v)=(r/2)*z i:=by
    simp [dotProduct,v,Pi.single_apply,mul_ite,ite_mul,mul_comm]
  rw [he]
  exact mul_ne_zero (by linarith) hi

theorem sr_body_covariance_positive_definite (K : Set (ι → ℝ))
    (compact : IsCompact K) (zeroInterior : K∈𝓝 (0:ι → ℝ)) :
    (srBodyCovariance K).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sr_covariance_is_hermitian K)
  intro z hz
  simp only [star_trivial]
  rw [sr_covariance_quadratic_is_integral K compact]
  let f:(ι → ℝ) → ℝ:=fun y=>(z ⬝ᵥ y)^2
  have hc:Continuous f:=by dsimp [f,dotProduct];fun_prop
  have hi:IntegrableOn f K:=hc.continuousOn.integrableOn_compact compact
  apply (integral_pos_iff_support_of_nonneg (fun y=>sq_nonneg (z ⬝ᵥ y)) hi).mpr
  rw [Measure.restrict_apply hc.isOpen_support.measurableSet]
  obtain ⟨y,hy,hn⟩:=sr_nonzero_linear_query_has_occupied_interior_answer K zeroInterior z hz
  let U:Set (ι → ℝ):=interior K∩Function.support f
  have hU:IsOpen U:=isOpen_interior.inter hc.isOpen_support
  have hpos:0<volume U:=hU.measure_pos volume ⟨y,hy,pow_ne_zero 2 hn⟩
  exact lt_of_lt_of_le hpos (measure_mono (by
    intro p hp
    exact ⟨hp.2,interior_subset hp.1⟩))

#print axioms sr_covariance_is_hermitian
#print axioms sr_covariance_quadratic_is_integral
#print axioms sr_nonzero_linear_query_has_occupied_interior_answer
#print axioms sr_body_covariance_positive_definite
end
end AASCMetricConstruction
