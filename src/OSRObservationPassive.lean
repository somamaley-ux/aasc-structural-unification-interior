import OSRLicensedNetworkOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def transportRadarAnswer (B : SRMatrixFrame) (c : SREvent) (answer : RadarAnswer) : RadarAnswer :=
  {answer with events := answer.events.map (frameEvent B c)}

theorem actual_radar_answer_passive (B : SRMatrixFrame) (c : SREvent) (d : NetworkData a s Omega n)
    (index : ℕ) (r : ExchangeRequest n) :
    actualRadarAnswer a s Omega n (passiveNetworkData a s Omega n B c d) index r=
      transportRadarAnswer B c (actualRadarAnswer a s Omega n d index r) := by
  simp [actualRadarAnswer,passiveNetworkData,requestRelay,transportRadarAnswer,List.map_map,
    Function.comp_def,frame_event_composition]

theorem actual_radar_read_and_failure_passive (B : SRMatrixFrame) (c : SREvent) (d : NetworkData a s Omega n)
    (index : ℕ) (correction : ℝ) :
    radarRead a s Omega n (passiveNetworkData a s Omega n B c d) index correction=
      (radarRead a s Omega n d index correction).map (transportRadarAnswer B c) := by
  simp only [radarRead,passive_network_request_domain]
  split
  · simp only [passiveNetworkData,Option.map_map]
    congr 1
    funext r
    exact actual_radar_answer_passive a s Omega n B c d index r
  · rfl

def transportSignalLedger (B : SRMatrixFrame) (c : SREvent) (ledger : SignalLedger) : SignalLedger :=
  {ledger with
    mainEvent := frameEvent B c ledger.mainEvent
    mainMomentum := srMatrixFrameEventLinear B ledger.mainMomentum
    compensatorEvent := frameEvent B c ledger.compensatorEvent
    compensatorMomentum := srMatrixFrameEventLinear B ledger.compensatorMomentum}

theorem actual_signal_ledger_events_momenta_identities_passive (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (r : ExchangeRequest n) (T : ℝ) :
    signalLedger a s Omega n (passiveNetworkData a s Omega n B c d) index r T=
      transportSignalLedger B c (signalLedger a s Omega n d index r T) := by
  simp only [signalLedger,passiveNetworkData,requestRelay,transportSignalLedger,sr_event_frame_mul,frame_event_composition]

theorem signal_read_and_failure_passive (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (T : ℝ) :
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.signal index T)=
      (networkDataObserve a s Omega n d (.signal index T)).map (transportSignalLedger B c) := by
  simp only [networkDataObserve,passiveNetworkData]
  split
  · simp only [Option.map_map]
    congr 1
    funext r
    exact actual_signal_ledger_events_momenta_identities_passive a s Omega n B c d index r T
  · rfl

theorem protocol_and_reference_are_retained_under_passive (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) :
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) .protocolContext=
      networkDataObserve a s Omega n d .protocolContext ∧
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) .referenceSelection=
      networkDataObserve a s Omega n d .referenceSelection := ⟨rfl,rfl⟩

end AASCKleinGordon.OperationalSR
