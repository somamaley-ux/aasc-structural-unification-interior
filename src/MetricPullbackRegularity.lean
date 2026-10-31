import QuadraticCoordinateJacobian
import LorentzMetricPullbackJet

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem coordinateMetricPullback_symmetric (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (F : CoordinatePoint → CoordinatePoint) : MetricFieldSymmetric (coordinateMetricPullback g F) := by
  intro x a b
  unfold coordinateMetricPullback
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [symmetric (F x) j i]
  ring

theorem coordinateJacobian_contDiffAt (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (smooth : ContDiffAt ℝ ⊤ F p) (i a : Fin 4) :
    ContDiffAt ℝ ⊤ (fun x => coordinateJacobian F x i a) p := by
  have hi : ContDiffAt ℝ ⊤ (fun x => F x i) p :=
    (coordinateProjection i).contDiff.contDiffAt.comp p smooth
  have hd : ContDiffAt ℝ ⊤ (fderiv ℝ (fun x => F x i)) p :=
    hi.fderiv_right (m := ⊤) (by simp)
  have hc : ContDiffAt ℝ ⊤ (fun _ : CoordinatePoint => (Pi.single a 1 : CoordinatePoint)) p :=
    contDiffAt_const
  exact hd.clm_apply hc

theorem coordinateMetricPullback_contDiffAt (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (p : CoordinatePoint) (smoothF : ContDiffAt ℝ ⊤ F p)
    (smoothG : ∀ i j, ContDiffAt ℝ ⊤ (fun x => g x i j) (F p)) (a b : Fin 4) :
    ContDiffAt ℝ ⊤ (fun x => coordinateMetricPullback g F x a b) p := by
  unfold coordinateMetricPullback
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((coordinateJacobian_contDiffAt F p smoothF i a).mul
    ((smoothG i j).comp p smoothF)).mul (coordinateJacobian_contDiffAt F p smoothF j b)

theorem quadratic_metric_pullback_value (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) :
    coordinateMetricPullback g (quadraticCoordinateMap p B Q) 0 =
      (coordinateFrameMatrix B).transpose * g p * coordinateFrameMatrix B := by
  ext a b
  simp only [coordinateMetricPullback, quadraticCoordinateMap_jacobian_zero p B Q symmetric,
    quadraticCoordinateMap_zero]
  exact matrix_pullback_double_sum _ _ a b

#print axioms coordinateMetricPullback_symmetric
#print axioms coordinateJacobian_contDiffAt
#print axioms coordinateMetricPullback_contDiffAt
#print axioms quadratic_metric_pullback_value
end
end AASCSemanticExhaustion
