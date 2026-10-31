import KGSourceDualTransport

/-! The continuation is the existing original raw Poincare action. Its quantum
and metric-source squares are proved afterward. Receiving regions and admission
charts move; the original complete-record content carrier is not a fixed box. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

theorem kg_interior_original_ray_continuation (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω) :
    kgInteriorOriginalRay a s Ω (kgOriginalRecordContinuation a s Ω q x)=
      wickPoincareRayAction a q.left.toAdd q.right (kgInteriorOriginalRay a s Ω x) := by
  induction x using Quotient.inductionOn with | _ u => rfl

theorem kg_interior_quantum_continuation (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω) :
    kgInteriorQuantum a s Ω (kgOriginalRecordContinuation a s Ω q x)=
      unitaryRayMap (kgCorePoincareIsometry a q) (kgInteriorQuantum a s Ω x) := by
  have source := kg_original_quantum_record_continuation a s Ω q (kgInteriorQuantum a s Ω x)
  rw [kg_interior_quantum_record_right_inverse] at source
  exact (congrArg (kgInteriorQuantum a s Ω) source).symm.trans
    (kg_interior_quantum_record_left_inverse a s Ω _)

theorem kg_interior_chart_continuation (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (D : Set (MetricSourceProbe V))
    (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω)
    (π : WickChartMetricPathProtocol V D) :
    kgInteriorChartReadout a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
      (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
      (kgOriginalRecordContinuation a s Ω q x) (wickChartMetricPathProtocolPoincare a q π)=
      kgInteriorChartReadout a s Ω V D x π := by
  induction x using Quotient.inductionOn with
  | _ u => exact wick_complete_metric_path_output_poincare a s q V D u π

theorem kg_interior_complete_original_continuation (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω)
    (π : WickMetricPathRoleProtocol Ω) :
    kgInteriorChartReadout a s Ω (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickTransportedMetricDomain q.left.toAdd q.right Ω)
      (kgOriginalRecordContinuation a s Ω q x)
      (wickChartMetricPathProtocolPoincare a q (wickOriginalMetricPathInChart π))=
      wickIdentifiedMetricPathRecordReadout a s Ω x π :=
  (kg_interior_chart_continuation a s Ω Ω (wickOriginalMetricNeighborhood Ω) q x
    (wickOriginalMetricPathInChart π)).trans (kg_interior_same_original_chart a s Ω x π)

theorem kg_interior_first_response_continuation (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω)
    (H : MetricSourceProbe V) :
    kgInteriorFirstResponseAt a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
      (kgOriginalRecordContinuation a s Ω q x) (wickNativeAffineMetricTest q.left.toAdd q.right H)=
      kgInteriorFirstResponseAt a s Ω V x H := by
  rw [kg_interior_first_response_at_original_ray,kg_interior_first_response_at_original_ray,
    kg_interior_original_ray_continuation]
  exact wick_original_ray_source_poincare a q.left.toAdd q.right s V
    (kgInteriorOriginalRay a s Ω x) H

theorem kg_interior_first_response_inverse_transport (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω) :
    kgInteriorFirstResponseAt a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
      (kgOriginalRecordContinuation a s Ω q x)=
      (kgInteriorFirstResponseAt a s Ω V x).comp (wickNativeAffineMetricInverseCLM q.left.toAdd q.right V) := by
  ext J
  have square := kg_interior_first_response_continuation a s Ω V q x
    (wickNativeAffineMetricInverseCLM q.left.toAdd q.right V J)
  rw [wick_native_affine_inverse_right] at square
  exact square

theorem kg_interior_metric_source_continuation (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω) :
    kgInteriorMetricSourceAt a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
      (kgOriginalRecordContinuation a s Ω q x)=
      kgMetricSourceTransport q V (kgInteriorMetricSourceAt a s Ω V x) := by
  calc
    _ = representedMetricSource (kgInteriorFirstResponseAt a s Ω
        (wickAffineMetricRegion q.left.toAdd q.right V) (kgOriginalRecordContinuation a s Ω q x)) :=
      constructed_metric_source_unique _ _ (kg_interior_at_half_pairing a s Ω _ _)
    _ = representedMetricSource ((kgInteriorFirstResponseAt a s Ω V x).comp
        (wickNativeAffineMetricInverseCLM q.left.toAdd q.right V)) :=
      congrArg representedMetricSource (kg_interior_first_response_inverse_transport a s Ω V q x)
    _ = _ := by rw [kgMetricSourceTransport,kg_interior_half_response_at]

theorem kg_interior_chart_first_failure (a : Parameters) (s : ℝ)
    (Ω V : Opens CoordinatePoint) (D : Set (MetricSourceProbe V))
    (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω)
    (word : List (WickChartMetricPathProtocol V D)) :
    kgFirstFailure (fun π => KGFamilyReadout.extraction (some
      (kgInteriorChartReadout a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
        (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
        (kgOriginalRecordContinuation a s Ω q x) π)))
      (word.map (wickChartMetricPathProtocolPoincare a q))=
    kgFirstFailure (fun π => KGFamilyReadout.extraction (some
      (kgInteriorChartReadout a s Ω V D x π))) word :=
  kg_first_failure_map (wickChartMetricPathProtocolPoincare a q)
    (fun π => KGFamilyReadout.extraction (some
      (kgInteriorChartReadout a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
        (wickNativeAffineMetricTest q.left.toAdd q.right '' D)
        (kgOriginalRecordContinuation a s Ω q x) π)))
    (fun π => KGFamilyReadout.extraction (some (kgInteriorChartReadout a s Ω V D x π)))
    (fun π => congrArg (fun out => KGFamilyReadout.extraction (some out))
    (kg_interior_chart_continuation a s Ω V D q x π)) word

end AASCKleinGordon
