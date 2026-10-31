import OSRFiniteNetworkCoverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem actual_successful_radar_has_proper_open_domain
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phase : Fin (n+1) → ℝ) (i j : Fin (n+1))
    (distinct : sites j ≠ sites i) (emit delay energy : ℝ) (wait : 0 ≤ delay) (positive : 0 < energy) :
    ∃ d : NetworkData a s Omega n, networkSound a s Omega n d ∧ IsOpen d.region ∧ d.region ≠ univ ∧
      ∃ answer : RadarAnswer, radarRead a s Omega n d 0 delay=some answer ∧
        answer.length=‖sites j-sites i‖ := by
  let request : ExchangeRequest n := ⟨i,j,emit,delay,energy⟩
  let S : SiteData n := ⟨sites,fun _ => 0,phase⟩
  let R := relayAtSites S i j emit delay energy
  let hi := (relayReturn R).1
  let O := protocolTimeSlab (emit-2) (hi+2)
  let d : NetworkData a s Omega n :=
    {populatedNetworkData a s Omega n r H sites phase emit hi [request] with region := O}
  have geometry := relay_at_distinct_sites_geometry S i j distinct emit delay energy
  have lengthPos : 0 < ‖sites j-sites i‖ := geometry.1
  have period : emit < hi := by
    change emit < emit+2*‖sites j-sites i‖+delay
    linarith
  have sound : networkSound a s Omega n d := by
    refine ⟨?_,srNativeFrameComparisons.one_mem,period.le⟩
    intro k
    simpa [d,populatedNetworkData] using a.mass_pos
  have clockCoverage : ∀ X : SRSpace, segmentCovered O (emit,X) (hi,X) := by
    intro X
    apply time_slab_full_segment <;> change emit-2 < _ ∧ _ < hi+2 <;> constructor <;> linarith
  have inverse : frameInverse (1:SRMatrixFrame) (0:SREvent)=id := by
    funext p
    simp [frameInverse,sr_event_frame_one]
  have domain : requestDomain a s Omega n d 0 delay := by
    refine ⟨request,rfl,rfl,rfl,rfl,Or.inr rfl,distinct,positive,wait,rfl,?_,le_refl _,le_refl _,?_,?_⟩
    · right
      change segmentCovered O (frameEvent 1 0 (emit,relayZ R)) (frameEvent 1 0 (hi,relayZ R))
      simpa [frameEvent,sr_event_frame_one] using clockCoverage (relayZ R)
    · change relayCovered (frameInverse 1 0 '' O) R
      rw [inverse,Set.image_id]
      exact (relay_proper_restricted_domain_populated R geometry.1 wait).1
    · intro k
      change segmentCovered O (frameEvent 1 0 (emit,sites k)) (frameEvent 1 0 (hi,sites k))
      simpa [frameEvent,sr_event_frame_one] using clockCoverage (sites k)
  refine ⟨d,sound,protocol_time_slab_open _ _,?_,actualRadarAnswer a s Omega n d 0 request,?_,?_⟩
  · exact (relay_proper_restricted_domain_populated R geometry.1 wait).2
  · rw [radarRead,if_pos domain]
    rfl
  · exact (occupied_network_radar_answer a s Omega n d sound 0 request).2

end AASCKleinGordon.OperationalSR
