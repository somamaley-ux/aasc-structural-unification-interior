import SKGMetricRayProtocol

/-! Every declared compact symmetric tangent has an admitted open ray
germ, hence actual nondegenerate projected metrics near zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology
namespace AASCKleinGordon.SameActionSource

theorem same_metric_ray_admitted_and_nondegenerate (a : Parameters)
    (h : MetricSourceProbe (sourceDomain a)) :
    ∀ᶠ t : ℝ in 𝓝 0,
      scalarMetricRayOperand a h t ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
        ∀ p : CoordinatePoint, (originalEHActMetric (scalarMetricRayOperand a h t) p).det < 0 := by
  filter_upwards [same_metric_ray_admitted_near_zero a h] with t admitted
  exact ⟨admitted, fun p => original_eh_act_metric_negative _ admitted p⟩

end AASCKleinGordon.SameActionSource
