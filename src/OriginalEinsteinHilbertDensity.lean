import EHGeometryTransport
import NativeClockHilbertSourceComponents

/-! The scalar density of the ORIGINAL gravitational summand of WDW-4B (71),
imported by CSP-C. Its curvature is computed by the actual LC connection.
No rank-two response, Einstein expression or classifier law is a data field.
These are density laws; the Euler first-variation identity remains separate. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Topology BigOperators

def originalEHScalarDensity (κ Λ : ℝ) (g : MetricField) (p : CoordinatePoint) : ℝ :=
  coordinateVolumeDensity g p * (coordinateScalarCurvature g p - 2 * Λ) / (2 * κ)

theorem original_metric_volume_density_pullback (g : MetricField)
    (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint) :
    coordinateVolumeDensity (coordinateMetricPullback g F) p =
      |(coordinateJacobian F p).det| * coordinateVolumeDensity g (F p) := by
  unfold coordinateVolumeDensity
  rw [coordinateMetricPullback_matrix,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
  rw [show -((coordinateJacobian F p).det * (g (F p)).det *
      (coordinateJacobian F p).det) = (coordinateJacobian F p).det ^ 2 * (-(g (F p)).det) by ring]
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

/-- Actual nonlinear coordinate covariance, with the density weight retained.
It is not the tensor transformation law of a presumed response. -/
theorem original_eh_density_natural (κ Λ : ℝ) (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) (F p))
    (nondegenerate : (g (F p)).det ≠ 0) (regularF : ContDiffAt ℝ 3 F p)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap p) :
    originalEHScalarDensity κ Λ (coordinateMetricPullback g F) p =
      |(coordinateJacobian F p).det| * originalEHScalarDensity κ Λ g (F p) := by
  rw [originalEHScalarDensity,original_metric_volume_density_pullback,
    coordinate_scalar_regular_natural g symmetric F p regularG nondegenerate regularF B derivative]
  unfold originalEHScalarDensity
  ring

theorem original_eh_density_twojet_local (κ Λ : ℝ) (g h : MetricField) (p : CoordinatePoint)
    (symmetricG : MetricFieldSymmetric g) (symmetricH : MetricFieldSymmetric h)
    (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (regularH : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) p)
    (nondegenerateG : (g p).det ≠ 0) (nondegenerateH : (h p).det ≠ 0)
    (equal : MetricTwoJetEqualAt g h p) :
    originalEHScalarDensity κ Λ g p = originalEHScalarDensity κ Λ h p := by
  have curv := c2_general_curvature_twojet_congr g h p symmetricG symmetricH
    regularG regularH nondegenerateG nondegenerateH equal
  simp only [originalEHScalarDensity,coordinateVolumeDensity,coordinateScalarCurvature,
    coordinateRicci,equal.1,curv]

theorem original_eh_normal_scalar_curvature (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) :
    coordinateScalarCurvature g 0 = scalarCurvatureResponse (originalNormalizedCurvature g germ) := by
  rw [scalarCurvatureResponse_eq_contraction,ricciResponse_eq_tensorRicci]
  change matrixContractionLinear (g 0)⁻¹
      (tensorRicci (g 0)⁻¹ (loweredConnectionCurvature g (leviCivitaCoefficients g) 0)) =
    matrixContractionLinear metric
      (tensorRicci metric (loweredConnectionCurvature g (leviCivitaCoefficients g) 0))
  rw [germ.2.2.1,canonical_metric_inverse]

theorem original_eh_density_normal_evaluation (κ Λ : ℝ) (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) :
    originalEHScalarDensity κ Λ g 0 =
      (scalarCurvatureResponse (originalNormalizedCurvature g germ) - 2 * Λ) / (2 * κ) := by
  rw [originalEHScalarDensity,c2_normal_metric_volume_value g (original_smooth_normalized_is_c2 g germ),
    one_mul,original_eh_normal_scalar_curvature g germ]

theorem original_eh_flat_scalar_curvature_zero : coordinateScalarCurvature flatMetricField 0 = 0 := by
  have germ : NormalizedSmoothMetricGerm flatMetricField := by
    rw [← hessianMetricPolynomial_flat]
    exact hessianMetricPolynomial_normalized 0
  have curv : originalNormalizedCurvature flatMetricField germ = 0 := by
    change c2NormalizedLeviCivitaCurvature flatMetricField _ = 0
    rw [c2_normalizedLeviCivitaCurvature_eq_jet]
    unfold c2NormalizedMetricJetCurvature
    have hh : c2MetricHessian flatMetricField 0 germ.1
        (original_smooth_normalized_is_c2 flatMetricField germ).2.1 = 0 := by
      apply Subtype.ext
      funext a b c d
      simp [c2MetricHessian,flatMetricField,scalarSecondPartial,scalarPartial]
    rw [hh,map_zero]
  rw [original_eh_normal_scalar_curvature flatMetricField germ,curv,map_zero]

theorem original_eh_density_flat_baseline (κ Λ : ℝ) :
    originalEHScalarDensity κ Λ flatMetricField 0 = -Λ / κ := by
  rw [originalEHScalarDensity,original_eh_flat_scalar_curvature_zero]
  have germ : C2NormalizedMetricGerm flatMetricField := by
    rw [← hessianMetricPolynomial_flat]
    exact original_smooth_normalized_is_c2 _ (hessianMetricPolynomial_normalized 0)
  rw [c2_normal_metric_volume_value _ germ]
  ring

/-- First-curvature affinity is DERIVED for the actual scalar Lagrangian.
The homogeneous volume/cosmological baseline is kept. No such law for the
not-yet-constructed rank-two Euler response is asserted here. -/
theorem original_eh_density_actual_curvature_add (κ Λ : ℝ) (g h k : MetricField)
    (hg : NormalizedSmoothMetricGerm g) (hh : NormalizedSmoothMetricGerm h)
    (hk : NormalizedSmoothMetricGerm k)
    (curvature : originalNormalizedCurvature k hk =
      originalNormalizedCurvature g hg + originalNormalizedCurvature h hh) :
    originalEHScalarDensity κ Λ k 0 = originalEHScalarDensity κ Λ g 0 +
      originalEHScalarDensity κ Λ h 0 - originalEHScalarDensity κ Λ flatMetricField 0 := by
  rw [original_eh_density_normal_evaluation κ Λ k hk,
    original_eh_density_normal_evaluation κ Λ g hg,
    original_eh_density_normal_evaluation κ Λ h hh,
    original_eh_density_flat_baseline,curvature,map_add]
  ring

theorem original_eh_density_actual_curvature_smul (κ Λ r : ℝ) (g k : MetricField)
    (hg : NormalizedSmoothMetricGerm g) (hk : NormalizedSmoothMetricGerm k)
    (curvature : originalNormalizedCurvature k hk = r • originalNormalizedCurvature g hg) :
    originalEHScalarDensity κ Λ k 0 = r *
      (originalEHScalarDensity κ Λ g 0 - originalEHScalarDensity κ Λ flatMetricField 0) +
        originalEHScalarDensity κ Λ flatMetricField 0 := by
  rw [original_eh_density_normal_evaluation κ Λ k hk,
    original_eh_density_normal_evaluation κ Λ g hg,
    original_eh_density_flat_baseline,curvature,map_smul]
  change (r * _ - 2 * Λ) / (2 * κ) = _
  ring

end
end AASCSemanticExhaustion
