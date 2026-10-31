import NormalChartFrameTransport

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem lorentz_adjoint_left_inverse (A : Tensor2)
    (preserved : A.transpose * metric * A = metric) :
    (metric * A.transpose * metric) * A = 1 := by
  calc
    _ = metric * (A.transpose * metric * A) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [preserved, canonical_metric_square]

def lorentzComparisonOfPreserved (A : Tensor2) (preserved : A.transpose * metric * A = metric) :
    LorentzComparison where
  forward := A
  inverse := metric * A.transpose * metric
  left_inverse := lorentz_adjoint_left_inverse A preserved
  right_inverse := mul_eq_one_comm.mp (lorentz_adjoint_left_inverse A preserved)
  metric_preserved := preserved

theorem normalized_chart_jacobian_preserves_metric (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (zero : F 0 = 0) (normal : C2NormalizedMetricGerm (coordinateMetricPullback g F)) :
    (coordinateJacobian F 0).transpose * metric * coordinateJacobian F 0 = metric := by
  have h := normal.2.2.1
  rw [coordinateMetricPullback_matrix, zero, germ.2.2.1] at h
  exact h

theorem coordinate_derivative_of_lorentz_jacobian (F : CoordinatePoint → CoordinatePoint)
    (regular : DifferentiableAt ℝ F 0) (L : LorentzComparison)
    (jacobian : coordinateJacobian F 0 = L.forward) :
    fderiv ℝ F 0 = (lorentzCoordinateEquiv L).toContinuousLinearMap := by
  have hb (a : Fin 4) : fderiv ℝ F 0 (Pi.single a 1) = lorentzCoordinateEquiv L (Pi.single a 1) := by
    ext i
    rw [← coordinateJacobian_vector F 0 regular, jacobian, lorentzCoordinateEquiv_basis]
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ F 0 v = lorentzCoordinateEquiv L v
  have h := continuousLinearMap_four_coordinates (fderiv ℝ F 0).toLinearMap v
  have h' := continuousLinearMap_four_coordinates (lorentzCoordinateEquiv L).toContinuousLinearMap.toLinearMap v
  change fderiv ℝ F 0 v = ∑ a : Fin 4, v a • fderiv ℝ F 0 (Pi.single a 1) at h
  change lorentzCoordinateEquiv L v = ∑ a : Fin 4, v a • lorentzCoordinateEquiv L (Pi.single a 1) at h'
  rw [h, h']
  simp_rw [hb]

/-- Full actual curvature transport between arbitrary C² normalized metric
germs under C³ coordinate maps. Lorentz comparison and the vanishing second
coordinate jet are derived from the two metric normalizations. -/
theorem c2_normal_chart_curvature_transport (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (zero : F 0 = 0)
    (normal : C2NormalizedMetricGerm (coordinateMetricPullback g F)) :
    loweredConnectionCurvature (coordinateMetricPullback g F)
      (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
        pullbackFour (coordinateJacobian F 0)
          (loweredConnectionCurvature g (leviCivitaCoefficients g) 0) := by
  let L := lorentzComparisonOfPreserved (coordinateJacobian F 0)
    (normalized_chart_jacobian_preserves_metric g germ F zero normal)
  have first := coordinate_derivative_of_lorentz_jacobian F
    (regular.differentiableAt (by norm_num)) L rfl
  exact c2_normal_chart_frame_curvature_transport g germ F regular zero L first normal

theorem c2_normal_chart_actual_local_inverse (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (zero : F 0 = 0)
    (normal : C2NormalizedMetricGerm (coordinateMetricPullback g F)) :
    ∃ e : OpenPartialHomeomorph CoordinatePoint CoordinatePoint,
      0 ∈ e.source ∧ (e : CoordinatePoint → CoordinatePoint) = F := by
  let L := lorentzComparisonOfPreserved (coordinateJacobian F 0)
    (normalized_chart_jacobian_preserves_metric g germ F zero normal)
  have first := coordinate_derivative_of_lorentz_jacobian F
    (regular.differentiableAt (by norm_num)) L rfl
  have hd : HasFDerivAt F (lorentzCoordinateEquiv L).toContinuousLinearMap 0 := by
    simpa only [first] using (regular.differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨regular.toOpenPartialHomeomorph F hd (by norm_num), ?_, rfl⟩
  exact regular.mem_toOpenPartialHomeomorph_source hd (by norm_num)

#print axioms lorentz_adjoint_left_inverse
#print axioms normalized_chart_jacobian_preserves_metric
#print axioms coordinate_derivative_of_lorentz_jacobian
#print axioms c2_normal_chart_curvature_transport
#print axioms c2_normal_chart_actual_local_inverse
end
end AASCSemanticExhaustion
