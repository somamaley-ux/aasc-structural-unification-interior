import TensorMetricContraction
import ActualCoordinateResponseExhaustion

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem lorentz_frame_inverse_metric_recovery (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) :
    (g p)⁻¹ = coordinateFrameMatrix B * metric * (coordinateFrameMatrix B).transpose := by
  apply Matrix.inv_eq_right_inv
  rw [lorentz_frame_metric_recovery g p B frame]
  have ht : (coordinateFrameMatrix B.symm).transpose * (coordinateFrameMatrix B).transpose = 1 := by
    rw [← Matrix.transpose_mul, coordinateFrameMatrix_right_inverse, Matrix.transpose_one]
  calc
    _ = (coordinateFrameMatrix B.symm).transpose * metric *
        (coordinateFrameMatrix B.symm * coordinateFrameMatrix B) * metric * (coordinateFrameMatrix B).transpose := by
      simp only [Matrix.mul_assoc]
    _ = (coordinateFrameMatrix B.symm).transpose * (metric * metric) * (coordinateFrameMatrix B).transpose := by
      rw [coordinateFrameMatrix_left_inverse]
      simp only [mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [canonical_metric_square, mul_one, ht]

theorem framedActualConnectionCurvature_ricci (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    ricciResponse (framedActualConnectionCurvature g p B symmetric regular frame) =
      (coordinateFrameMatrix B).transpose * coordinateRicci g p * coordinateFrameMatrix B := by
  rw [ricciResponse_eq_tensorRicci]
  exact tensorRicci_pullback (coordinateFrameMatrix B) metric (g p)⁻¹
    (loweredConnectionCurvature g (leviCivitaCoefficients g) p)
      (lorentz_frame_inverse_metric_recovery g p B frame).symm

theorem framedActualConnectionCurvature_scalar (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    scalarCurvatureResponse (framedActualConnectionCurvature g p B symmetric regular frame) =
      coordinateScalarCurvature g p := by
  rw [scalarCurvatureResponse_eq_contraction,
    framedActualConnectionCurvature_ricci g p B symmetric regular frame,
    matrixContraction_pullback, ← lorentz_frame_inverse_metric_recovery g p B frame]
  rfl

theorem framedActualConnectionCurvature_scalar_metric (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    scalarMetricResponse (framedActualConnectionCurvature g p B symmetric regular frame) =
      coordinateScalarCurvature g p • metric := by
  change scalarCurvatureResponse (framedActualConnectionCurvature g p B symmetric regular frame) • metric = _
  rw [framedActualConnectionCurvature_scalar g p B symmetric regular frame]

theorem lorentz_frame_scalar_metric_pullback (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    (coordinateFrameMatrix B).transpose * coordinateScalarMetric g p * coordinateFrameMatrix B =
      scalarMetricResponse (framedActualConnectionCurvature g p B symmetric regular frame) := by
  rw [framedActualConnectionCurvature_scalar_metric g p B symmetric regular frame]
  change (coordinateFrameMatrix B).transpose * (coordinateScalarCurvature g p • g p) * coordinateFrameMatrix B = _
  rw [Matrix.mul_smul, Matrix.smul_mul, frame]

theorem frame_matrix_pullback_injective (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    Function.Injective (fun M : Tensor2 => (coordinateFrameMatrix B).transpose * M * coordinateFrameMatrix B) := by
  intro M N h
  have he := congrArg (fun A : Tensor2 =>
    (coordinateFrameMatrix B.symm).transpose * A * coordinateFrameMatrix B.symm) h
  dsimp only at he
  rw [inverse_frame_metric_recovery M B, inverse_frame_metric_recovery N B] at he
  exact he

theorem actual_coordinate_response_identity_iff (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B)
    (T : Tensor2) (a b c : ℝ) :
    (coordinateFrameMatrix B).transpose * T * coordinateFrameMatrix B =
      a • ricciResponse (framedActualConnectionCurvature g p B symmetric regular frame) +
        b • scalarMetricResponse (framedActualConnectionCurvature g p B symmetric regular frame) + c • metric ↔
      T = a • coordinateRicci g p + b • coordinateScalarMetric g p + c • g p := by
  have hPB : (coordinateFrameMatrix B).transpose *
      (a • coordinateRicci g p + b • coordinateScalarMetric g p + c • g p) * coordinateFrameMatrix B =
      a • ricciResponse (framedActualConnectionCurvature g p B symmetric regular frame) +
        b • scalarMetricResponse (framedActualConnectionCurvature g p B symmetric regular frame) + c • metric := by
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [← framedActualConnectionCurvature_ricci g p B symmetric regular frame,
      lorentz_frame_scalar_metric_pullback g p B symmetric regular frame, frame]
  constructor
  · intro h
    exact frame_matrix_pullback_injective B (h.trans hPB.symm)
  · intro h
    rw [h]
    exact hPB

#print axioms lorentz_frame_inverse_metric_recovery
#print axioms framedActualConnectionCurvature_ricci
#print axioms framedActualConnectionCurvature_scalar
#print axioms framedActualConnectionCurvature_scalar_metric
#print axioms lorentz_frame_scalar_metric_pullback
#print axioms frame_matrix_pullback_injective
#print axioms actual_coordinate_response_identity_iff
end
end AASCSemanticExhaustion
