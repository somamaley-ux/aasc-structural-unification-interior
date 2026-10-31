import MetricNormalizationTransition

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem coordinateJacobian_of_derivative_equiv (F : CoordinatePoint → CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap 0) :
    coordinateJacobian F 0 = coordinateFrameMatrix B := by
  ext i a
  rw [coordinateJacobian_vector F 0 derivative.differentiableAt, derivative.fderiv]
  rfl

theorem frame_metric_pullback_nondegenerate (G : Tensor2) (nondegenerate : G.det ≠ 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    ((coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B).det ≠ 0 := by
  have h := congrArg Matrix.det (coordinateFrameMatrix_right_inverse B)
  simp only [Matrix.det_mul, Matrix.det_one] at h
  have hB : (coordinateFrameMatrix B).det ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at h
    norm_num at h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hB nondegenerate) hB

/-- Actual curvature tensoriality at the origin for every nondegenerate C²
metric and C³ local coordinate map with an explicitly invertible derivative.
No metric-value normalization or first-derivative restriction remains. -/
theorem c2_coordinate_leviCivita_curvature_natural_zero (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (regularG : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (nondegenerate : (g 0).det ≠ 0) (F : CoordinatePoint → CoordinatePoint)
    (regularF : ContDiffAt ℝ 3 F 0) (zeroF : F 0 = 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap 0) :
    loweredConnectionCurvature (coordinateMetricPullback g F) (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
      pullbackFour (coordinateJacobian F 0) (loweredConnectionCurvature g (leviCivitaCoefficients g) 0) := by
  let h := coordinateMetricPullback g F
  let ng := coordinateMetricPullback g (normalizingCoordinateMap g)
  let nh := coordinateMetricPullback h (normalizingCoordinateMap h)
  let T := metricNormalizationTransition g F
  have symH : MetricFieldSymmetric h := coordinateMetricPullback_symmetric g symmetric F
  have regH : ∀ a b, ContDiffAt ℝ 2 (fun x => h x a b) 0 :=
    c3_coordinateMetricPullback_c2 g F regularF (by simpa only [zeroF] using regularG)
  have frameF := coordinateJacobian_of_derivative_equiv F B derivative
  have ndH : (h 0).det ≠ 0 := by
    change (coordinateMetricPullback g F 0).det ≠ 0
    rw [coordinateMetricPullback_matrix, zeroF, frameF]
    exact frame_metric_pullback_nondegenerate (g 0) nondegenerate B
  have symNG : MetricFieldSymmetric ng := coordinateMetricPullback_symmetric g symmetric _
  have symNH : MetricFieldSymmetric nh := coordinateMetricPullback_symmetric h symH _
  have regNG := c2_general_normalizing_metric_regular g regularG
  have regNH := c2_general_normalizing_metric_regular h regH
  have ndNG : (ng 0).det ≠ 0 := by
    change (coordinateMetricPullback g (normalizingCoordinateMap g) 0).det ≠ 0
    rw [general_normalizing_metric_value g symmetric]
    exact nondegenerate
  have ndNH : (nh 0).det ≠ 0 := by
    change (coordinateMetricPullback h (normalizingCoordinateMap h) 0).det ≠ 0
    rw [general_normalizing_metric_value h symH]
    exact ndH
  have firstNG := c2_general_normalizing_metric_first_zero g symmetric regularG nondegenerate
  have firstNH := c2_general_normalizing_metric_first_zero h symH regH ndH
  have regularT : ContDiffAt ℝ 3 T 0 := metricNormalizationTransition_c3 g F regularF zeroF
  have zeroT : T 0 = 0 := metricNormalizationTransition_zero g F zeroF
  have frameT := coordinateJacobian_of_derivative_equiv T B
    (metricNormalizationTransition_hasFDerivAt g F regularF zeroF B derivative)
  have equal := metric_twojet_of_eventuallyEq (coordinateMetricPullback ng T) nh 0
    (metricNormalizationTransition_metric_eventually g F regularF zeroF)
  have regNGT := c3_coordinateMetricPullback_c2 ng T regularT (by simpa only [zeroT] using regNG)
  have ndNGT : (coordinateMetricPullback ng T 0).det ≠ 0 := by rw [equal.1]; exact ndNH
  have firstNGT : ∀ a b, fderiv ℝ (fun x => coordinateMetricPullback ng T x a b) 0 = 0 := by
    intro a b
    exact (equal.2.1 a b).trans (firstNH a b)
  have hcongr := c2_general_curvature_twojet_congr (coordinateMetricPullback ng T) nh 0
    (coordinateMetricPullback_symmetric ng symNG T) symNH regNGT regNH ndNGT ndNH equal
  have hflat := c2_first_flat_general_chart_curvature_transport ng symNG regNG ndNG firstNG T regularT
    zeroT B frameT ndNGT firstNGT
  have hnormG := c2_normalizing_actual_curvature_preserved g symmetric regularG nondegenerate
  have hnormH := c2_normalizing_actual_curvature_preserved h symH regH ndH
  calc
    loweredConnectionCurvature h (leviCivitaCoefficients h) 0 =
        loweredConnectionCurvature nh (leviCivitaCoefficients nh) 0 := hnormH.symm
    _ = loweredConnectionCurvature (coordinateMetricPullback ng T)
        (leviCivitaCoefficients (coordinateMetricPullback ng T)) 0 := hcongr.symm
    _ = pullbackFour (coordinateJacobian T 0) (loweredConnectionCurvature ng (leviCivitaCoefficients ng) 0) := hflat
    _ = pullbackFour (coordinateJacobian F 0) (loweredConnectionCurvature g (leviCivitaCoefficients g) 0) := by
      rw [hnormG, frameT, frameF]

#print axioms coordinateJacobian_of_derivative_equiv
#print axioms frame_metric_pullback_nondegenerate
#print axioms c2_coordinate_leviCivita_curvature_natural_zero
end
end AASCSemanticExhaustion
