import OSRNetworkPopulation
import OSRActualNetworkRadar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem populated_network_every_declared_valid_request_is_executed
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ)
    (schedule : List (ExchangeRequest n)) (index : ℕ) (request : ExchangeRequest n)
    (registered : schedule[index]?=some request)
    (distinct : sites request.toSite ≠ sites request.fromSite) (energy : 0 < request.energy)
    (delay : 0 ≤ request.delay) (start : lo ≤ request.emit)
    (finish : request.emit+2*‖sites request.toSite-sites request.fromSite‖+request.delay ≤ hi) :
    requestDomain a s Omega n (populatedNetworkData a s Omega n r H sites phases lo hi schedule) index request.delay := by
  let d := populatedNetworkData a s Omega n r H sites phases lo hi schedule
  have inverse : frameInverse (1:SRMatrixFrame) (0:SREvent)=id := by
    funext p
    simp [frameInverse,sr_event_frame_one]
  refine ⟨request,registered,rfl,rfl,rfl,Or.inr rfl,distinct,energy,delay,rfl,?_,start,finish,?_,?_⟩
  · right
    intro t ht
    trivial
  · change relayCovered (frameInverse 1 0 '' Set.univ) _
    rw [inverse,Set.image_id]
    exact relay_whole_affine_domain_populated _
  · intro i t ht
    trivial

theorem populated_network_radar_success_is_inhabited
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) :
    ∃ d : NetworkData a s Omega 1, networkSound a s Omega 1 d ∧
      ∃ answer : RadarAnswer, radarRead a s Omega 1 d 0 2=some answer ∧ answer.length=1 := by
  let sites : Fin 2 → SRSpace := fun i => if i=0 then 0 else srFirstSpatialUnit
  let request : ExchangeRequest 1 := ⟨0,1,0,2,1⟩
  let d := populatedNetworkData a s Omega 1 r H sites (fun _ => 0) 0 4 [request]
  have length : ‖sites 1-sites 0‖=1 := by simp [sites,sr_first_spatial_unit_norm]
  have distinct : sites 1 ≠ sites 0 := by
    intro same
    have zero : ‖sites 1-sites 0‖=0 := by simp [same]
    linarith
  have domain : requestDomain a s Omega 1 d 0 2 :=
    populated_network_every_declared_valid_request_is_executed a s Omega 1 r H sites (fun _ => 0) 0 4 [request]
      0 request rfl distinct (by norm_num [request]) (by norm_num [request]) (by norm_num [request])
      (by simpa [request,length] using (show (0:ℝ)+2*1+2 ≤ 4 by norm_num))
  have sound : networkSound a s Omega 1 d :=
    populated_network_actual_sound a s Omega 1 r H sites (fun _ => 0) 0 4 (by norm_num) [request]
  refine ⟨d,sound,actualRadarAnswer a s Omega 1 d 0 request,?_,?_⟩
  · rw [radarRead,if_pos domain]
    rfl
  · simpa [d,populatedNetworkData,request,length] using
      (occupied_network_radar_answer a s Omega 1 d sound 0 request).2

end AASCKleinGordon.OperationalSR
