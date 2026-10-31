import TensorPullbackComposition

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem coordinateFrameMatrix_mul_apply (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (i a : Fin 4) :
    (coordinateFrameMatrix B * coordinateFrameMatrix C) i a = B (C (Pi.single a 1)) i := by
  have h := congrArg (fun v : CoordinatePoint => v i)
    (continuousLinearMap_four_coordinates B.toContinuousLinearMap.toLinearMap (C (Pi.single a 1)))
  change B (C (Pi.single a 1)) i = ∑ j : Fin 4, (C (Pi.single a 1)) j * (B (Pi.single j 1)) i at h
  simpa only [coordinateFrameMatrix, Matrix.mul_apply, mul_comm] using h.symm

theorem coordinateFrameMatrix_right_inverse (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    coordinateFrameMatrix B * coordinateFrameMatrix B.symm = 1 := by
  ext i a
  rw [coordinateFrameMatrix_mul_apply]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem coordinateFrameMatrix_left_inverse (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    coordinateFrameMatrix B.symm * coordinateFrameMatrix B = 1 := by
  simpa only [ContinuousLinearEquiv.symm_symm] using coordinateFrameMatrix_right_inverse B.symm

theorem pointNormalChartTransition_inverse_frame_equation (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    coordinateJacobian (pointNormalChartTransition g p B C symmetric) 0 * coordinateFrameMatrix C.symm =
      coordinateFrameMatrix B.symm := by
  have h := congrArg (fun A : Tensor2 => coordinateFrameMatrix B.symm * A)
    (pointNormalChartTransition_frame_equation g p B C symmetric)
  simp only [← Matrix.mul_assoc, coordinateFrameMatrix_left_inverse, one_mul] at h
  rw [h, Matrix.mul_assoc, coordinateFrameMatrix_right_inverse, mul_one]

/-- Curvature components reconstructed in the original coordinate frame from
an actual normal chart. Independence is proved below. Identification with the
original non-normal-coordinate connection formula remains a separate theorem. -/
def reconstructedCoordinateCurvature (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) : Tensor4 :=
  pullbackFour (coordinateFrameMatrix B.symm) (c2_normalChartCurvature g p B symmetric regular frame)

theorem reconstructedCoordinateCurvature_frame_independent (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (frameB : LorentzFrameAt g p B) (frameC : LorentzFrameAt g p C) :
    reconstructedCoordinateCurvature g p C symmetric regular frameC =
      reconstructedCoordinateCurvature g p B symmetric regular frameB := by
  unfold reconstructedCoordinateCurvature
  rw [c2_point_normal_chart_curvature_comparison g p B C symmetric regular frameB frameC,
    pullbackFour_comp, pointNormalChartTransition_inverse_frame_equation g p B C symmetric]

#print axioms coordinateFrameMatrix_mul_apply
#print axioms coordinateFrameMatrix_right_inverse
#print axioms coordinateFrameMatrix_left_inverse
#print axioms pointNormalChartTransition_inverse_frame_equation
#print axioms reconstructedCoordinateCurvature_frame_independent
end
end AASCSemanticExhaustion
