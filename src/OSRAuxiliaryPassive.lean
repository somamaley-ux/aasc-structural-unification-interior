import OSRMarkedComposition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem auxiliary_actual_clock_full_marked_state_passive (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d)
    (r : ExchangeRequest n) (T : ℝ) :
    let original : SRClockRecord := (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))
    let time := srPassiveMarkedTime a.mass d.frame d.origin original T
    srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n (passiveNetworkData a s Omega n B c d) r)
      (srPassiveMarkedTime a.mass (B*d.frame) (frameEvent B c d.origin) original T)=
    transportMarkedState a.mass B c time (srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n d r) time) := by
  exact passive_full_marked_state_composition a.mass a.mass_pos B d.frame admitted sound.2.1 c d.origin
    (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))
    (by simpa [srNativeClockMass,srNativeRestClock] using a.mass_pos) T

end AASCKleinGordon.OperationalSR
