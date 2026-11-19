import SRFrameConeRigidity

/-!
# Inertial interval identification by ten readings

In native event coordinates the nine non-rest probes are null increments.
The remaining comparison measures the squared interval of the transported
unit rest increment. The competitor is an arbitrary real matrix.
-/

namespace AASCProjectionCoverage

open AASCMetricConstruction AASCMetricConstruction.SRIntegration
open AASCKleinGordon.CanonicalLicensing.SRIntegration
open scoped Matrix

/-- Nine null readings and one rest reading exactly characterize preservation
of the native Lorentz form by an arbitrary real-linear comparison. -/
theorem finite_inertial_readings_iff (A : ComparisonMatrix) :
    ((∀ i : Fin 10, i ≠ 0 →
        comparisonQuadratic comparisonUnitLorentz (A.mulVec (originalComparisonProbe i)) = 0) ∧
      comparisonQuadratic comparisonUnitLorentz (A.mulVec (originalComparisonProbe 0)) = 1) ↔
    srFramePullback A = comparisonUnitLorentz := by
  constructor
  · rintro ⟨nullReadings, restReading⟩
    have null : ∀ i : Fin 10, i ≠ 0 → comparisonAnswers (srFramePullback A) i = 0 := by
      intro i hi
      exact (sr_frame_pullback_quadratic A _).trans (nullReadings i hi)
    have rest : comparisonAnswers (srFramePullback A) 0 = 1 :=
      (sr_frame_pullback_quadratic A _).trans restReading
    have reconstruction := reconstruct_null_answers _ null
    rwa [comparison_reconstruction_recovers_every_symmetric_receipt _
      (sr_frame_pullback_symmetric A), rest, one_smul] at reconstruction
  · intro preserves
    constructor
    · intro i hi
      rw [← sr_frame_pullback_quadratic, preserves]
      exact sr_original_finite_probe_is_null i hi
    · rw [← sr_frame_pullback_quadratic, preserves]
      norm_num [comparisonQuadratic, comparisonUnitLorentz, originalComparisonProbe,
        Matrix.diagonal, Fin.sum_univ_succ]

/-- The same finite data give invertibility and equality at every increment.
They do not distinguish time or spatial orientation. -/
theorem finite_inertial_readings_determine_all_increments (A : ComparisonMatrix)
    (nullReadings : ∀ i : Fin 10, i ≠ 0 →
      comparisonQuadratic comparisonUnitLorentz (A.mulVec (originalComparisonProbe i)) = 0)
    (restReading : comparisonQuadratic comparisonUnitLorentz
      (A.mulVec (originalComparisonProbe 0)) = 1) :
    IsUnit A ∧ ∀ v : ComparisonVector,
      comparisonQuadratic comparisonUnitLorentz (A.mulVec v) =
        comparisonQuadratic comparisonUnitLorentz v := by
  have preserves := (finite_inertial_readings_iff A).1 ⟨nullReadings, restReading⟩
  constructor
  · apply (Matrix.isUnit_iff_isUnit_det A).2
    apply isUnit_iff_ne_zero.mpr
    intro zero
    have h := congrArg Matrix.det preserves
    simp [srFramePullback, Matrix.det_mul, comparison_unit_lorentz_det, zero] at h
  · intro v
    rw [← sr_frame_pullback_quadratic, preserves]

#print axioms finite_inertial_readings_iff
#print axioms finite_inertial_readings_determine_all_increments

end AASCProjectionCoverage
