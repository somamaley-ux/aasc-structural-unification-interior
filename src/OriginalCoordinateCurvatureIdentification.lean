import C2GeneralPointCurvatureNaturality

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem inverse_frame_metric_recovery (G : Tensor2) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    (coordinateFrameMatrix B.symm).transpose *
      ((coordinateFrameMatrix B).transpose * G * coordinateFrameMatrix B) * coordinateFrameMatrix B.symm = G := by
  have ht : (coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose = 1 := by
    rw [← Matrix.transpose_mul, coordinateFrameMatrix_right_inverse, Matrix.transpose_one]
  calc
    _ = ((coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose) * G *
        (coordinateFrameMatrix B * coordinateFrameMatrix B.symm) := by simp only [Matrix.mul_assoc]
    _ = G := by rw [ht, coordinateFrameMatrix_right_inverse, one_mul, mul_one]

theorem lorentz_frame_metric_recovery (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) :
    g p = (coordinateFrameMatrix B.symm).transpose * metric * coordinateFrameMatrix B.symm := by
  have h := congrArg (fun A : Tensor2 =>
    (coordinateFrameMatrix B.symm).transpose * A * coordinateFrameMatrix B.symm) frame
  dsimp only at h
  rw [inverse_frame_metric_recovery] at h
  exact h

theorem lorentz_frame_metric_nondegenerate (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) : (g p).det ≠ 0 := by
  rw [lorentz_frame_metric_recovery g p B frame]
  apply frame_metric_pullback_nondegenerate metric _ B.symm
  rw [canonical_lorentz_metric_det]
  norm_num

/-- The actual constructed normal-chart curvature is the tensor pullback of
the original non-normal-coordinate Levi-Civita connection curvature. -/
theorem c2_normalChartCurvature_eq_actual_pullback (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    ((c2_normalChartCurvature g p B symmetric regular frame : curvatureSpace) : Tensor4) =
      pullbackFour (coordinateFrameMatrix B) (loweredConnectionCurvature g (leviCivitaCoefficients g) p) := by
  have hn := c2_coordinate_leviCivita_curvature_natural_at_target g p symmetric regular
    (lorentz_frame_metric_nondegenerate g p B frame) (pointNormalChartMap g p B)
      ((pointNormalChartMap_analytic g p B).contDiffAt.of_le (by simp))
      (pointNormalChartMap_zero g p B) B (pointNormalChartMap_hasFDerivAt g p B symmetric)
  rw [pointNormalChartMap_pullback, pointNormalChartMap_jacobian g p B symmetric] at hn
  exact hn

/-- The frame-independent reconstructed tensor is identified with the original
actual connection curvature at every supplied Lorentzian C² metric point. -/
theorem reconstructedCoordinateCurvature_eq_original_connection (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    reconstructedCoordinateCurvature g p B symmetric regular frame =
      loweredConnectionCurvature g (leviCivitaCoefficients g) p := by
  unfold reconstructedCoordinateCurvature
  rw [c2_normalChartCurvature_eq_actual_pullback g p B symmetric regular frame, pullbackFour_comp,
    coordinateFrameMatrix_right_inverse, pullbackFour_identity]

#print axioms inverse_frame_metric_recovery
#print axioms lorentz_frame_metric_recovery
#print axioms lorentz_frame_metric_nondegenerate
#print axioms c2_normalChartCurvature_eq_actual_pullback
#print axioms reconstructedCoordinateCurvature_eq_original_connection
end
end AASCSemanticExhaustion
