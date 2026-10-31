import OSRAuxiliaryPassive
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem old_licensed_consumer_has_actual_passive_source (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n) (i : Fin (n+1)) :
    licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n (licensedNetworkPassive a s Omega n B admitted c r) i)=
      (⟨srPassiveClockUse a.mass B c (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).clock,
        (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).scalar,
        (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).metric⟩ : JointOriginalSource a s Omega) := by
  exact congrArg (fun clock => (⟨clock,(licensedNetworkSource a s Omega n r).data.scalar,
    (licensedNetworkSource a s Omega n r).data.metric⟩ : JointOriginalSource a s Omega))
    (network_passive_source_is_same_actual_old_clock a s Omega n B admitted c _
      (licensed_network_has_actual_sound_source a s Omega n r) i)

end AASCKleinGordon.OperationalSR
