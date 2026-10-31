import SKGCompactWard
import RegularSourceTestSeparation

/-! An occupied Cauchy datum has nonzero actual stress and an actual
nonzero compact metric response; the zero solution is not the witness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem same_source_time_time (a : Parameters) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    sameSourceStress a u p 0 0 = (1 / 2 : ℝ) *
      (scalarPartial u p 0 ^ 2 + (∑ i : Fin 3, scalarPartial u p i.succ ^ 2) +
        massWaveNumber a ^ 2 * sourceFactor a p * u p ^ 2) := by
  rw [sameSourceStress, source_metric_conformal,
    scalar_conformal_stress_polynomial _ u _ p (source_factor_nonzero a p)]
  simp [scalarConformalStressPolynomial, scalarFlatKinetic, metric,
    Matrix.diagonal_apply, Fin.sum_univ_succ]
  ring

theorem actual_source_time_time_density (a : Parameters) (u : CoordinatePoint → ℝ)
    (p : CoordinatePoint) : actualSourceDensityCoordinates a u 0 p = sameSourceStress a u p 0 0 := by
  change raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u) p 0 0 = _
  rw [same_source_raised_density]
  norm_num [metric, Matrix.diagonal_apply]

def occupiedSourceField (a : Parameters) : CoordinatePoint → ℝ :=
  sourceField a (occupiedCompactCauchyPosition a) 0

theorem occupied_source_field_smooth (a : Parameters) :
    ContDiff ℝ (⊤ : ℕ∞) (occupiedSourceField a) := source_field_smooth a _ _

theorem occupied_source_stress_positive (a : Parameters) :
    0 < sameSourceStress a (occupiedSourceField a) 0 0 0 := by
  have value : occupiedSourceField a 0 = 1 := occupied_curved_cauchy_field_nonzero a
  rw [same_source_time_time, value, one_pow, mul_one]
  have mass := sq_pos_of_ne_zero (massWaveNumber_ne_zero a)
  have potential := mul_pos mass (source_factor_positive a 0)
  have spatial : 0 ≤ ∑ i : Fin 3, scalarPartial (occupiedSourceField a) 0 i.succ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  positivity

theorem occupied_actual_compact_metric_response (a : Parameters) :
    ∃ protocol : ScalarMetricRayProtocol a,
      scalarMetricRayOutput a (occupiedSourceField a) protocol ≠ 0 := by
  let regular := scalarSmoothTwo (occupiedSourceField a) (occupied_source_field_smooth a)
  by_contra absent
  push_neg at absent
  have zeroTest (psi : ScalarSourceProbe (sourceDomain a)) :
      ∫ p, actualSourceDensityCoordinates a (occupiedSourceField a) 0 p * psi p = 0 := by
    unfold actualSourceDensityCoordinates
    rw [← same_action_source_represents_actual_stress a _ regular 0 psi]
    unfold sameActionScalarSource representedMetricSource
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [← same_action_ray_output_is_constructed_response a _ regular
      ⟨sourceTestInsertion 0 psi⟩, absent, mul_zero]
  have zeroAt := continuous_scalar_source_tests_separate (sourceDomain a)
    (actualSourceDensityCoordinates a (occupiedSourceField a) 0)
    (actual_source_density_smooth a _ (occupied_source_field_smooth a) 0).continuous zeroTest
    0 (source_domain_zero a)
  rw [actual_source_time_time_density] at zeroAt
  exact (ne_of_gt (occupied_source_stress_positive a)) zeroAt

end AASCKleinGordon.SameActionSource
