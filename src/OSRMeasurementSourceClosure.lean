import OSRLicensedNetworkOperations
import OSRRotatedMeasurement

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem retained_measuring_answer_is_same_actual_clock (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (Q : MeasuringQuery) (i j : Fin (n+1)) :
    let answer := actualMeasuringAnswer a s Omega n d Q i j
    let ti := srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i) (measuringSiteTime Q (d.sites.position i))
    let tj := srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites j) (measuringSiteTime Q (d.sites.position j))
    answer.firstEvent=srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d i).clock.record ti ∧
    answer.secondEvent=srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d j).clock.record tj ∧
    answer.firstReading=(srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n d i).clock.record ti).2.reading ∧
    answer.secondReading=(srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n d j).clock.record tj).2.reading := by
  exact ⟨(raw_network_clock_actual_same_event a s Omega n d sound i _).symm,
    (raw_network_clock_actual_same_event a s Omega n d sound j _).symm,
    (raw_network_clock_actual_same_reading a s Omega n d sound i _).symm,
    (raw_network_clock_actual_same_reading a s Omega n d sound j _).symm⟩

theorem original_coordinate_ruler_is_retained_query_specialization (d : NetworkData a s Omega n)
    (i j : Fin (n+1)) (T : ℝ) :
    rulerRead a s Omega n d i j T=
      (measuringRead a s Omega n d ⟨d.frame,d.origin,T⟩ i j).map
        (fun answer => (answer.firstEvent,answer.secondEvent,answer.length)) := by
  simp only [rulerRead,measuringRead,rulerDomain]
  split <;> rfl

theorem licensed_measuring_read_same_question_passive (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)) :
    licensedNetworkObserve a s Omega n (licensedNetworkPassive a s Omega n B admitted c r)
      (.original (.measuring Q i j))=
      (licensedNetworkObserve a s Omega n r (.original (.measuring Q i j))).map (transportMeasuringAnswer B c) :=
  measuring_read_same_question_transport_and_failure a s Omega n B c _ Q i j

theorem registered_protocol_ledger_is_exactly_retained (x : NetworkSource a s Omega n) :
    networkCompleteObserve a s Omega n x (.original .protocolContext)=
      (x.data.schedule,x.data.clockResource,x.data.signalResource,x.data.relayResource) := rfl

end AASCKleinGordon.OperationalSR
