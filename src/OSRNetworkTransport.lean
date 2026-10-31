import OSRNetworkSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem raw_network_clock_actual_same_event (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (t : ℝ) :
    srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d i).clock.record
      (srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i) t)=
      frameEvent d.frame d.origin (t,d.sites.position i) := by
  have actual := sr_passive_same_marked_clock_event_square a.mass a.mass_pos
    (srNativeOccupiedFrameSource a.mass a.mass_pos) d.frame sound.2.1 d.origin
    (siteRecord a.mass d.sites i) t (sound.1 i)
  rw [site_actual_event a.mass d.sites i (sound.1 i)] at actual
  exact actual

theorem raw_network_clock_actual_same_reading (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (t : ℝ) :
    (srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n d i).clock.record
      (srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i) t)).2.reading=
      siteReading a.mass d.sites i t :=
  sr_passive_same_marked_clock_reading_square a.mass a.mass_pos (srNativeOccupiedFrameSource a.mass a.mass_pos)
    d.frame sound.2.1 d.origin (siteRecord a.mass d.sites i) t (sound.1 i)

theorem measured_network_endpoints_are_actual_same_clocks (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (T : ℝ) :
    srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d i).clock.record
      (srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i)
        (selectedSiteTime d.frame d.origin T (d.sites.position i)))=
      measuredEndpoint d.frame d.origin T (d.sites.position i) :=
  raw_network_clock_actual_same_event a s Omega n d sound i _

theorem relay_extra_endpoint_actual_passive_event_and_reading (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (r : ExchangeRequest n) (T : ℝ) :
    let R := requestRelay a s Omega n d r
    let original : SRClockRecord := (0,0,srNativeRestClock (relayZ R))
    srMarkedClockEvent a.mass (relayClockRecord a s Omega n d r)
      (srPassiveMarkedTime a.mass d.frame d.origin original T)=frameEvent d.frame d.origin (T,relayZ R) ∧
    (srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n d r)
      (srPassiveMarkedTime a.mass d.frame d.origin original T)).2.reading=T := by
  dsimp only
  let original : SRClockRecord := (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))
  have positive : 0 < srNativeClockMass a.mass original.2.2 :=
    (sr_native_positive_rest_clock_is_occupied a.mass a.mass_pos _).1
  have event := sr_passive_same_marked_clock_event_square a.mass a.mass_pos
    (srNativeOccupiedFrameSource a.mass a.mass_pos) d.frame sound.2.1 d.origin original T positive
  have reading := sr_passive_same_marked_clock_reading_square a.mass a.mass_pos
    (srNativeOccupiedFrameSource a.mass a.mass_pos) d.frame sound.2.1 d.origin original T positive
  have actual := sr_native_rest_clock_actual_coasting_record a.mass a.mass_pos
    (relayZ (requestRelay a s Omega n d r)) T
  have originalEvent : srMarkedClockEvent a.mass original T=(T,relayZ (requestRelay a s Omega n d r)) := by
    apply Prod.ext
    · rfl
    · simpa [srMarkedClockEvent,srNativeCoastingMarkedRecord,original] using actual.1
  rw [originalEvent] at event
  refine ⟨event,?_⟩
  change (srNativeCoastingMarkedRecord a.mass (srPassiveClockRecord a.mass d.frame d.origin original)
    (srPassiveMarkedTime a.mass d.frame d.origin original T)).2.reading=T
  exact reading.trans (by simpa [srNativeCoastingMarkedRecord,original] using actual.2.1)

end AASCKleinGordon.OperationalSR
