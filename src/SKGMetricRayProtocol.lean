import SKGSameMetricRegularity

/-! The new classical scalar protocols are actual compact metric rays in the
old admitted operand carrier. This is fixed before constructing a tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def liftSourceMetricTest {U : Opens CoordinatePoint} (h : MetricSourceProbe U) :
    MetricSourceProbe (⊤ : Opens CoordinatePoint) :=
  ⟨h, h.contDiff, h.hasCompactSupport, by intro p hp; trivial⟩

theorem lift_source_metric_test_apply {U : Opens CoordinatePoint}
    (h : MetricSourceProbe U) (p : CoordinatePoint) : liftSourceMetricTest h p = h p := rfl

def scalarMetricRayOperand (a : Parameters) {U : Opens CoordinatePoint}
    (h : MetricSourceProbe U) (t : ℝ) : MetricSourceProbe (⊤ : Opens CoordinatePoint) :=
  conformalOperand (conformalFrequency a) + t • liftSourceMetricTest h

theorem same_metric_ray_admitted_near_zero (a : Parameters) {U : Opens CoordinatePoint}
    (h : MetricSourceProbe U) :
    ∀ᶠ t : ℝ in 𝓝 0, scalarMetricRayOperand a h t ∈
      wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) := by
  have regular : Continuous (fun t : ℝ => scalarMetricRayOperand a h t) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have initial : scalarMetricRayOperand a h 0 ∈
      wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) := by
    simpa [scalarMetricRayOperand] using conformal_operand_admitted (conformalFrequency a)
  exact regular.continuousAt ((wick_original_metric_neighborhood_open _).mem_nhds initial)

theorem same_metric_ray_projected_metric (a : Parameters) {U : Opens CoordinatePoint}
    (h : MetricSourceProbe U) (t : ℝ) (p : CoordinatePoint) :
    originalEHActMetric (scalarMetricRayOperand a h t) p =
      fun i j => sourceMetric a p i j + t * tensorEncode (h p) i j := by
  have addEncoding (x y : Fin 10 → ℝ) :
      tensorEncode (x + y) = tensorEncode x + tensorEncode y := tensorEncodeLinear.map_add x y
  have scalarEncoding (r : ℝ) (x : Fin 10 → ℝ) :
      tensorEncode (r • x) = r • tensorEncode x := tensorEncodeLinear.map_smul r x
  funext i j
  change wickNativeFlatMetric p i j + tensorEncode
    (conformalOperand (conformalFrequency a) p + t • h p) i j = _
  rw [addEncoding, scalarEncoding]
  change wickNativeFlatMetric p i j + (tensorEncode (conformalOperand (conformalFrequency a) p) i j +
      t * tensorEncode (h p) i j) =
    (wickNativeFlatMetric p i j + tensorEncode (conformalOperand (conformalFrequency a) p) i j) +
      t * tensorEncode (h p) i j
  ring

theorem same_metric_ray_actual_tangent (a : Parameters) {U : Opens CoordinatePoint}
    (h : MetricSourceProbe U) (p : CoordinatePoint) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => originalEHActMetric (scalarMetricRayOperand a h t) p i j)
      (tensorEncode (h p) i j) 0 := by
  have equal : (fun t : ℝ => originalEHActMetric (scalarMetricRayOperand a h t) p i j) =
      fun t => sourceMetric a p i j + t * tensorEncode (h p) i j := by
    funext t
    rw [same_metric_ray_projected_metric]
  rw [equal]
  simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (tensorEncode (h p) i j)).const_add
    (sourceMetric a p i j))

structure ScalarMetricRayProtocol (a : Parameters) where
  test : MetricSourceProbe (sourceDomain a)

def scalarMetricRayAction (a : Parameters) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) (t : ℝ) : ℝ :=
  nativeScalarClockRelativeAction (sourceMetric a) u (massWaveNumber a ^ 2) (t • protocol.test)

def scalarMetricRayOutput (a : Parameters) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) : ℝ := deriv (scalarMetricRayAction a u protocol) 0

def scalarMetricRayIncidence (a : Parameters) (h : MetricSourceProbe (sourceDomain a))
    (protocol : ScalarMetricRayProtocol a) : Prop := protocol.test = h

theorem scalar_ray_is_same_action_metric_axis (a : Parameters) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) (t : ℝ) :
    scalarMetricRayAction a u protocol t =
      sameEHJointRelativeAction a u (fun _ => 0) protocol.test t 0 := by
  exact (same_eh_joint_action_metric_axis a u (fun _ => 0) protocol.test t).symm

end AASCKleinGordon.SameActionSource
