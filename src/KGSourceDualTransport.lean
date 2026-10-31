import KGOriginalInteriorReceivers

/-! Canonical dual transport of the actual tensor-density distribution.
Its all-test half-pairing functional is recovered, transported along the
proved inverse test map, then represented. No naturality certificate is input. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
open scoped BigOperators

def kgSourceHalfResponse {Ω : Opens CoordinatePoint} (T : SymmetricSourceComponents Ω) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  (1/2 : ℝ) • ∑ i : Fin 10,symmetricSourceWeight i • (T i).comp (sourceTestProjection i)

theorem kg_source_half_response_apply {Ω : Opens CoordinatePoint}
    (T : SymmetricSourceComponents Ω) (H : MetricSourceProbe Ω) :
    kgSourceHalfResponse T H=(1/2 : ℝ)*metricSourcePairing T H := by
  simp only [kgSourceHalfResponse,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,smul_eq_mul,metricSourcePairing]

theorem kg_source_half_response_representation {Ω : Opens CoordinatePoint}
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) :
    kgSourceHalfResponse (representedMetricSource W)=W := by
  ext H
  exact (kg_source_half_response_apply _ H).trans (constructed_metric_source_represents W H)

theorem kg_source_representation_half_response {Ω : Opens CoordinatePoint}
    (T : SymmetricSourceComponents Ω) : representedMetricSource (kgSourceHalfResponse T)=T :=
  (constructed_metric_source_unique (kgSourceHalfResponse T) T
    (fun H => (kg_source_half_response_apply T H).symm)).symm

theorem kg_interior_half_response_at (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (x : WickMetricPathQresp a s Ω) :
    kgSourceHalfResponse (kgInteriorMetricSourceAt a s Ω V x)=
      kgInteriorFirstResponseAt a s Ω V x := by
  ext H
  exact (kg_source_half_response_apply _ H).trans (kg_interior_at_half_pairing a s Ω V x H)

def kgMetricSourceTransport (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (T : SymmetricSourceComponents Ω) :
    SymmetricSourceComponents (wickAffineMetricRegion q.left.toAdd q.right Ω) :=
  representedMetricSource ((kgSourceHalfResponse T).comp
    (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω))

theorem kg_metric_source_transport_all_tests (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (T : SymmetricSourceComponents Ω)
    (J : MetricSourceProbe (wickAffineMetricRegion q.left.toAdd q.right Ω)) :
    (1/2 : ℝ)*metricSourcePairing (kgMetricSourceTransport q Ω T) J=
      (1/2 : ℝ)*metricSourcePairing T (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω J) :=
  (constructed_metric_source_represents _ J).trans
    (kg_source_half_response_apply T (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω J))

theorem kg_metric_source_transport_unique (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (T : SymmetricSourceComponents Ω)
    (S : SymmetricSourceComponents (wickAffineMetricRegion q.left.toAdd q.right Ω))
    (same : ∀ J,(1/2 : ℝ)*metricSourcePairing S J=
      (1/2 : ℝ)*metricSourcePairing T (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω J)) :
    S=kgMetricSourceTransport q Ω T := by
  apply constructed_metric_source_unique
  intro J
  exact (same J).trans (kg_source_half_response_apply T _).symm

end AASCKleinGordon
