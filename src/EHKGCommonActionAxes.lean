import EHKGRelativeActionIntegrability
import NativeScalarClockMetricAction

/-! Field and metric variations are axes of one displayed density protocol.
This retains the action ancestry for the later metric-source construction;
no Einstein coupling or source conservation is asserted here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def sameEHJointRelativeAction (a : Parameters) (u d : CoordinatePoint → ℝ)
    {Omega : Opens CoordinatePoint} (H : MetricSourceProbe Omega) (s t : ℝ) : ℝ :=
  ∫ p : CoordinatePoint,
    nativeRealClockDensity
      (fun i j => originalEHActMetric (conformalOperand (conformalFrequency a)) p i j +
        tensorEncode ((s • H) p) i j)
      (scalarPartial (fun q => u q + t * d q) p) (u p + t * d p) ((massWaveNumber a) ^ 2) -
    sameEHScalarDensity a u p

theorem same_eh_joint_action_field_axis (a : Parameters) (u d : CoordinatePoint → ℝ)
    {Omega : Opens CoordinatePoint} (H : MetricSourceProbe Omega) (t : ℝ) :
    sameEHJointRelativeAction a u d H 0 t = sameEHRelativeFieldAction a u d t := by
  have encodeZero : tensorEncode (0 : Fin 10 → ℝ) = 0 := tensorEncodeLinear.map_zero
  unfold sameEHJointRelativeAction sameEHRelativeFieldAction sameEHScalarDensity
  simp only [zero_smul]
  apply integral_congr_ae
  filter_upwards with p
  have zeroAt : (0 : MetricSourceProbe Omega) p = 0 := rfl
  rw [zeroAt, encodeZero]
  simp

theorem same_eh_joint_action_metric_axis (a : Parameters) (u d : CoordinatePoint → ℝ)
    {Omega : Opens CoordinatePoint} (H : MetricSourceProbe Omega) (s : ℝ) :
    sameEHJointRelativeAction a u d H s 0 =
      nativeScalarClockRelativeAction (originalEHActMetric (conformalOperand (conformalFrequency a)))
        u ((massWaveNumber a) ^ 2) (s • H) := by
  simp only [sameEHJointRelativeAction, zero_mul, add_zero,
    nativeScalarClockRelativeAction, nativeActualClockMetricAction, nativeScalarClockGradient,
    sameEHScalarDensity]
  rfl

end AASCKleinGordon.CurvedKG
