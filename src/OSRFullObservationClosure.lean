import OSROldConsumerPassive
import OSRMeasurementSourceClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem auxiliary_endpoint_original_read_and_failure_transport (B : SRMatrixFrame)
    (admitted : B ∈ srNativeFrameComparisons) (c : SREvent) (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (index : ℕ) (r : ExchangeRequest n)
    (registered : d.schedule[index]?=some r) (T : ℝ) :
    let original : SRClockRecord := (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))
    let time := srPassiveMarkedTime a.mass d.frame d.origin original T
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.relayEndpoint index T)=
      (networkDataObserve a s Omega n d (.relayEndpoint index T)).map
        (fun answer => (answer.1,transportMarkedState a.mass B c time answer.2)) := by
  dsimp only
  simp only [networkDataObserve,passiveNetworkData,registered,Option.bind_some]
  split
  · simp only [Option.map_some]
    exact congrArg (fun record => some (index,record))
      (auxiliary_actual_clock_full_marked_state_passive a s Omega n B admitted c d sound r T)
  · rfl

theorem unregistered_auxiliary_failure_retained (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (T : ℝ) (unregistered : d.schedule[index]?=none) :
    networkDataObserve a s Omega n d (.relayEndpoint index T)=none ∧
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.relayEndpoint index T)=none := by
  simp [networkDataObserve,passiveNetworkData,unregistered]

theorem original_coordinate_ruler_same_question_transport (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (i j : Fin (n+1)) (T : ℝ) :
    (measuringRead a s Omega n (passiveNetworkData a s Omega n B c d) ⟨d.frame,d.origin,T⟩ i j).map
      (fun answer => (answer.firstEvent,answer.secondEvent,answer.length))=
    (rulerRead a s Omega n d i j T).map
      (fun answer => (frameEvent B c answer.1,frameEvent B c answer.2.1,answer.2.2)) := by
  rw [measuring_read_same_question_transport_and_failure,original_coordinate_ruler_is_retained_query_specialization,
    Option.map_map,Option.map_map]
  rfl

theorem site_event_and_reading_same_question_transport (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (i : Fin (n+1)) (T : ℝ) :
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.siteEvent i T)=
      frameEvent B c (networkDataObserve a s Omega n d (.siteEvent i T)) ∧
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.siteReading i T)=
      networkDataObserve a s Omega n d (.siteReading i T) := by
  exact ⟨(frame_event_composition B d.frame c d.origin _).symm,rfl⟩

def licensedNetworkToPhysical (r : LicensedNetworkReceiver a s Omega n) : NetworkReceiver a s Omega n :=
  presentNetwork a s Omega n (licensedNetworkSource a s Omega n r)

theorem full_licensed_operation_physical_refinement_square (op : NetworkOperation n)
    (r : LicensedNetworkReceiver a s Omega n) :
    (licensedNetworkOperation a s Omega n op r).map (licensedNetworkToPhysical a s Omega n)=
      networkReceiverOperation a s Omega n op (licensedNetworkToPhysical a s Omega n r) := by
  unfold licensedNetworkToPhysical
  rw [network_receiver_operation_square,←licensed_network_operation_actual_source_square a s Omega n op r,Option.map_map]
  rfl

end AASCKleinGordon.OperationalSR
