import NativeCalibratedMetricFromComparisons

/-! Finite-query algebra for SR 6.1. These lemmas do not select a metric
preserving frame group. The nine null answers must be supplied by the actual
source cone/boundary transport; scale removal remains a separate obligation. -/
namespace AASCMetricConstruction.SRIntegration
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Matrix BigOperators

def srFramePullback (A : ComparisonMatrix) : ComparisonMatrix :=
  A.transpose * comparisonUnitLorentz * A

theorem sr_comparison_unit_lorentz_symmetric :
    comparisonUnitLorentz.transpose = comparisonUnitLorentz := by
  ext i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [comparisonUnitLorentz,Matrix.diagonal,h,Ne.symm h]

theorem sr_frame_pullback_symmetric (A : ComparisonMatrix) :
    (srFramePullback A).transpose = srFramePullback A := by
  simp only [srFramePullback,Matrix.transpose_mul,Matrix.transpose_transpose,
    sr_comparison_unit_lorentz_symmetric,Matrix.mul_assoc]

theorem sr_frame_pullback_quadratic (A : ComparisonMatrix) (v : ComparisonVector) :
    comparisonQuadratic (srFramePullback A) v =
      comparisonQuadratic comparisonUnitLorentz (A.mulVec v) := by
  simp [comparisonQuadratic,srFramePullback,Matrix.mul_apply,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ,Matrix.transpose_apply]
  ring

theorem sr_original_null_boundary_queries_force_conformal_frame
    (A : ComparisonMatrix)
    (boundary : ∀ i : Fin 10, i ≠ 0 →
      comparisonQuadratic comparisonUnitLorentz (A.mulVec (originalComparisonProbe i)) = 0)
    (v : ComparisonVector) :
    comparisonQuadratic comparisonUnitLorentz (A.mulVec v) =
      comparisonAnswers (srFramePullback A) 0 * (v 0^2-v 1^2-v 2^2-v 3^2) := by
  have null : ∀ i : Fin 10, i ≠ 0 → comparisonAnswers (srFramePullback A) i = 0 := by
    intro i hi
    exact (sr_frame_pullback_quadratic A (originalComparisonProbe i)).trans (boundary i hi)
  have h := constructed_null_receipt_quadratic (comparisonAnswers (srFramePullback A)) null v
  rw [comparison_reconstruction_recovers_every_symmetric_receipt
      (srFramePullback A) (sr_frame_pullback_symmetric A)] at h
  exact (sr_frame_pullback_quadratic A v).symm.trans h

theorem sr_positive_frame_scale_constructed_from_original_clock_query
    (A : ComparisonMatrix)
    (clock : 0 < comparisonAnswers (srFramePullback A) 0) :
    0 < Real.sqrt (comparisonAnswers (srFramePullback A) 0) ∧
      Real.sqrt (comparisonAnswers (srFramePullback A) 0)^2 =
        comparisonAnswers (srFramePullback A) 0 :=
  ⟨Real.sqrt_pos.mpr clock,Real.sq_sqrt clock.le⟩

theorem sr_calibrated_rest_frame_has_unit_conformal_scale
    (A : ComparisonMatrix) (T : ℝ) (positive : 0 < T)
    (restPair : A.mulVec (T • originalComparisonProbe 0) = T • originalComparisonProbe 0) :
    comparisonAnswers (srFramePullback A) 0 = 1 := by
  have action : A.mulVec (originalComparisonProbe 0) = originalComparisonProbe 0 := by
    have h := restPair
    rw [Matrix.mulVec_smul] at h
    exact (smul_right_injective _ positive.ne') h
  rw [comparisonAnswers,sr_frame_pullback_quadratic,action]
  norm_num [comparisonQuadratic,comparisonUnitLorentz,originalComparisonProbe,
    Fin.sum_univ_succ,Matrix.diagonal]

#print axioms sr_original_null_boundary_queries_force_conformal_frame
#print axioms sr_calibrated_rest_frame_has_unit_conformal_scale
end
end AASCMetricConstruction.SRIntegration
