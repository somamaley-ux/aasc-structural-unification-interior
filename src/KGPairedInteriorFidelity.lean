import KGOriginalInteriorRegion

/-! A bounded output theorem for the declared original free-KG regime.
This records proved fidelity clauses and comparisons; it is not a full U48.1
or U6.2 physical-interior certificate. No compatibility or endpoint certificate
is accepted as an input. Active curved E30.1 and qualified NR S36.1 stay open. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion

structure KGOriginalPairedFidelity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Prop where
  metric_act_injective : Function.Injective (wickOriginalRoleMetricProjection Ω)
  metric_act_lorentzian : ∀ (H : WickKGAdmittedFiniteMetric Ω) (x : Spacetime),
    WickLorentzSignature (wickOriginalRoleMetricProjection Ω H x)
  metric_act_nondegenerate : ∀ (H : WickKGAdmittedFiniteMetric Ω) (x : Spacetime),
    (wickOriginalRoleMetricProjection Ω H x).det≠0
  quantum_injective : Function.Injective (kgInteriorQuantum a s Ω)
  metric_relative_faithful : ∀ x y : WickMetricPathQresp a s Ω,
    kgInteriorMetricSource a s Ω x=kgInteriorMetricSource a s Ω y ↔
      ∀ H : MetricSourceProbe Ω,kgInteriorFirstResponse a s Ω x H=kgInteriorFirstResponse a s Ω y H
  half_pairing : ∀ (x : WickMetricPathQresp a s Ω) (H : MetricSourceProbe Ω),
    (1/2 : ℝ)*metricSourcePairing (kgInteriorMetricSource a s Ω x) H=kgInteriorFirstResponse a s Ω x H
  actual_path_response : ∀ (x : WickMetricPathQresp a s Ω) (π : WickAdmittedC1MetricPath Ω),
    wickIdentifiedMetricPathRecordReadout a s Ω x (.path π)=
      .metric (.first (kgInteriorFirstResponse a s Ω x π.analytic.tangentTest))
  derived_standing : ∀ x : WickMetricPathQresp a s Ω,
    kgW9OriginalResponse a s Ω (kgInteriorQuantum a s Ω x)=x
  original_source : ∀ x : WickMetricPathQresp a s Ω,
    (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
      (wickCommonRoleSourcePresentation a s Ω (kgOriginalQuantumToRay a (kgInteriorQuantum a s Ω x))))).val=x
  raw_reference : ∀ (u : WickNonzeroCore)
    (π : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))),
    (kgInteriorReferences a s Ω).referenceAt (Quotient.mk (wickMetricPathRoleSetoid a s Ω) u) π=
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.referenceAt (kgRawOriginalEquiv a u) π
  determinate : (kgInteriorReferences a s Ω).incidenceSystem.Determinate
  source_attachment_tensor : ∀ x : WickMetricPathQresp a s Ω,
    wickRoleQg a s Ω (kgInteriorSourceAttachment a s Ω x)=kgInteriorMetricSource a s Ω x
  source_ledger_retained : ∀ x : WickMetricPathQresp a s Ω,
    kgInteriorSourceLedger a s Ω x=wickOriginalSourceLedgerValue Ω
  original_registered : ∀ (x : WickMetricPathQresp a s Ω) (π : WickMetricPathRoleProtocol Ω),
    kgInteriorRegisteredReadout a s Ω x (.original .original π)=
      .extraction (some (wickIdentifiedMetricPathRecordReadout a s Ω x π))
  quantum_continuation : ∀ (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω),
    kgInteriorQuantum a s Ω (kgOriginalRecordContinuation a s Ω q x)=
      unitaryRayMap (kgCorePoincareIsometry a q) (kgInteriorQuantum a s Ω x)
  metric_continuation : ∀ (V : Opens CoordinatePoint) (q : ProperPoincareTransform)
    (x : WickMetricPathQresp a s Ω),
    kgInteriorMetricSourceAt a s Ω (wickAffineMetricRegion q.left.toAdd q.right V)
      (kgOriginalRecordContinuation a s Ω q x)=kgMetricSourceTransport q V (kgInteriorMetricSourceAt a s Ω V x)
  complete_continuation : ∀ (q : ProperPoincareTransform) (x : WickMetricPathQresp a s Ω)
    (π : WickMetricPathRoleProtocol Ω),
    kgInteriorChartReadout a s Ω (wickAffineMetricRegion q.left.toAdd q.right Ω)
      (wickTransportedMetricDomain q.left.toAdd q.right Ω) (kgOriginalRecordContinuation a s Ω q x)
      (wickChartMetricPathProtocolPoincare a q (wickOriginalMetricPathInChart π))=
      wickIdentifiedMetricPathRecordReadout a s Ω x π
  regional_source : ∀ {V W : Opens CoordinatePoint} (h : V ≤ W) (x : WickMetricPathQresp a s Ω),
    kgMetricSourceRestriction h (kgInteriorMetricSourceAt a s Ω W x)=kgInteriorMetricSourceAt a s Ω V x

theorem kg_constructed_original_paired_fidelity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGOriginalPairedFidelity a s Ω where
  metric_act_injective := kg_original_metric_act_faithful Ω
  metric_act_lorentzian := kg_original_metric_act_lorentzian Ω
  metric_act_nondegenerate := kg_original_metric_act_nondegenerate Ω
  quantum_injective := kg_interior_quantum_faithful a s Ω
  metric_relative_faithful := kg_interior_metric_source_faithful a s Ω
  half_pairing := kg_interior_metric_half_pairing a s Ω
  actual_path_response := kg_interior_path_first_response a s Ω
  derived_standing := kg_interior_derived_standing_right_inverse a s Ω
  original_source := kg_interior_complete_source_square a s Ω
  raw_reference := kg_interior_reference_raw_square a s Ω
  determinate := kg_interior_reference_determinate a s Ω
  source_attachment_tensor := kg_interior_source_attachment_tensor a s Ω
  source_ledger_retained := kg_interior_source_ledger_exact a s Ω
  original_registered := kg_interior_registered_original_square a s Ω
  quantum_continuation := kg_interior_quantum_continuation a s Ω
  metric_continuation := kg_interior_metric_source_continuation a s Ω
  complete_continuation := kg_interior_complete_original_continuation a s Ω
  regional_source := kg_interior_regional_source a s Ω

theorem kg_constraint_first_original_paired_fidelity (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) :
    KGSpecificRawQP a s Ω ∧ KGSpecificStandingSource a s Ω ∧ KGOriginalPairedFidelity a s Ω :=
  ⟨kg_constructed_raw_qp a s Ω,kg_constraint_first_standing_source a s Ω,
    kg_constructed_original_paired_fidelity a s Ω⟩

end AASCKleinGordon
