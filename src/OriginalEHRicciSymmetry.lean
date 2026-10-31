import OriginalEHVolumeCompatibility
import OriginalEHPalatiniContractionAlgebra

/-! Symmetry of the actual general-coordinate Ricci contraction, derived
from the computed second-jet curvature formula and finite contractions. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

theorem eh_hessian_ricci_symmetric (B : Tensor2) (bs : ∀ i j, B i j = B j i)
    (H : metricHessianSpace) (a b : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, B i j * curvatureOfNormalHessian H i a j b) =
      ∑ i : Fin 4, ∑ j : Fin 4, B i j * curvatureOfNormalHessian H i b j a := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [bs j i,hessian_curvature_pair_exchange H j a i b]

theorem eh_quadratic_ricci_symmetric (B : Tensor2) (bs : ∀ i j, B i j = B j i)
    (L : Fin 4 → Fin 4 → Fin 4 → ℝ) (ls : ∀ a b c, L a b c = L a c b)
    (a b : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, B i j *
      (∑ k : Fin 4, (∑ l : Fin 4, B k l * L l i b) * L k a j)) =
      ∑ i : Fin 4, ∑ j : Fin 4, B i j *
        (∑ k : Fin 4, (∑ l : Fin 4, B k l * L l i a) * L k b j) := by
  have h : ehSum4 (fun i j k l => B i j * (B k l * L l i b) * L k a j) =
      ehSum4 (fun i j k l => B i j * (B k l * L l i a) * L k b j) := by
    calc
      _ = ehSum4 (fun i j k l => B j i * (B l k * L k j b) * L l a i) := by
        calc
          _ = ehSum4 (fun i j k l => B j i * (B k l * L l j b) * L k a i) :=
            eh_sum4_swap12 _
          _ = _ := eh_sum4_swap34 _
      _ = _ := by
        apply eh_sum4_congr
        intro i j k l
        rw [bs j i,bs l k,ls k j b,ls l a i]
        ring
  simpa only [ehSum4,Finset.mul_sum,Finset.sum_mul,mul_assoc] using h

theorem eh_actual_ricci_symmetric (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (hn : (g p).det ≠ 0) (a b : Fin 4) :
    coordinateRicci g p a b = coordinateRicci g p b a := by
  let B : Tensor2 := (g p)⁻¹
  let L := lowerChristoffel g p
  let H := c2MetricHessian g p sg (eh_smooth_metric_c2_at g hg p)
  have bs : ∀ i j, B i j = B j i := eh_inverse_symmetric g sg p
  have ls : ∀ i j k, L i j k = L i k j := lowerChristoffel_torsion_free g sg p
  have hH := eh_hessian_ricci_symmetric B bs H a b
  have hQ := eh_quadratic_ricci_symmetric B bs L ls a b
  have hQ' :
      (∑ i : Fin 4, ∑ j : Fin 4, B i j *
        (∑ k : Fin 4, leviCivitaCoefficients g p k i j * L k a b)) =
      ∑ i : Fin 4, ∑ j : Fin 4, B i j *
        (∑ k : Fin 4, leviCivitaCoefficients g p k i j * L k b a) := by
    simp only [ls _ a b]
  unfold coordinateRicci
  simp_rw [c2_general_coordinate_curvature_formula g p sg
    (eh_smooth_metric_c2_at g hg p) hn]
  change (∑ i : Fin 4, ∑ j : Fin 4, B i j *
      (curvatureOfNormalHessian H i a j b +
        (∑ k : Fin 4, leviCivitaCoefficients g p k i b * L k a j) -
        (∑ k : Fin 4, leviCivitaCoefficients g p k i j * L k a b))) =
    ∑ i : Fin 4, ∑ j : Fin 4, B i j *
      (curvatureOfNormalHessian H i b j a +
        (∑ k : Fin 4, leviCivitaCoefficients g p k i a * L k b j) -
        (∑ k : Fin 4, leviCivitaCoefficients g p k i j * L k b a))
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hH,hQ']
  congr 1
  congr 1

theorem eh_einstein_raised_matrix_symmetric (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (p : CoordinatePoint) (hn : (g p).det ≠ 0) (Λ : ℝ) (a b : Fin 4) :
    ((g p)⁻¹ * (coordinateRicci g p -
      (coordinateScalarCurvature g p / 2) • g p + Λ • g p) * (g p)⁻¹) a b =
    ((g p)⁻¹ * (coordinateRicci g p -
      (coordinateScalarCurvature g p / 2) • g p + Λ • g p) * (g p)⁻¹) b a := by
  have hs : (g p).transpose = g p := by
    ext i j
    exact sg p j i
  have hb : ((g p)⁻¹).transpose = (g p)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,hs]
  have hr : (coordinateRicci g p).transpose = coordinateRicci g p := by
    ext i j
    exact eh_actual_ricci_symmetric g sg hg p hn j i
  have ht : (((g p)⁻¹ * (coordinateRicci g p -
      (coordinateScalarCurvature g p / 2) • g p + Λ • g p) * (g p)⁻¹)).transpose =
      (g p)⁻¹ * (coordinateRicci g p -
        (coordinateScalarCurvature g p / 2) • g p + Λ • g p) * (g p)⁻¹ := by
    simp only [Matrix.transpose_mul,Matrix.transpose_add,Matrix.transpose_sub,
      Matrix.transpose_smul,hb,hr,hs,Matrix.mul_assoc]
  exact congrArg (fun M : Tensor2 => M b a) ht

end
end AASCSemanticExhaustion
