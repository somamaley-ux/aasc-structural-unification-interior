import OSRNetworkPassive

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem actual_site_passive_slope (mu0 : ℝ) {k : ℕ} (S : SiteData k) (i : Fin (k+1))
    (positive : 0 < mu0+S.internalEnergy i) (A : SRMatrixFrame) :
    srPassiveClockSlope mu0 A (siteRecord mu0 S i).2.2=observerSlope A := by
  change srNativeClockRate mu0 (directionalClock mu0 (S.internalEnergy i) restUnit (S.position i) (S.phase i))*
    (srMatrixFrameEventLinear A (srNativeProperTangent mu0
      (directionalClock mu0 (S.internalEnergy i) restUnit (S.position i) (S.phase i)))).1=observerSlope A
  rw [directional_clock_actual_rate mu0 _ positive restUnit restUnit_future,
    directional_clock_actual_proper_tangent mu0 _ positive restUnit restUnit_future]
  simp [restUnit,observerSlope]

theorem network_raw_use_is_actual_passive_rest_rebase (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) :
    (networkRawJoint a s Omega n x i).clock=srPassiveClockUse a.mass x.data.frame x.data.origin
      (srNativeClockUseRedescription a.mass (x.epoch i) (siteUse a.mass x.data.sites i x.data.lo x.data.hi)) := by
  have actual := sr_passive_clock_use_rebase a.mass a.mass_pos (srNativeOccupiedFrameSource a.mass a.mass_pos)
    x.data.frame sound.2.1 x.data.origin (siteUse a.mass x.data.sites i x.data.lo x.data.hi) (x.epoch i) (sound.1 i)
  simp only [siteUse] at actual
  rw [actual_site_passive_slope a.mass x.data.sites i (sound.1 i)] at actual
  exact actual.symm

theorem network_passive_source_is_same_actual_old_clock (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (x : NetworkSource a s Omega n) (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) :
    (networkRawJoint a s Omega n (passiveNetwork a s Omega n B c x) i).clock=
      srPassiveClockUse a.mass B c (networkRawJoint a s Omega n x i).clock := by
  rw [network_raw_use_is_actual_passive_rest_rebase a s Omega n _
    (passive_network_actually_sound a s Omega n B admitted c x.data sound) i,
    network_raw_use_is_actual_passive_rest_rebase a s Omega n x sound i]
  exact (sr_passive_clock_use_composition a.mass a.mass_pos (srNativeOccupiedFrameSource a.mass a.mass_pos)
    B x.data.frame sound.2.1 c x.data.origin _
      (by simpa [srNativeClockUseRedescription,srNativeClockRedescription,srNativeClockCoastFlow,srNativeClockMass,
        siteUse,siteRecord,directionalClock] using sound.1 i)).symm

end AASCKleinGordon.OperationalSR
