import OSRNetworkLicensing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def populatedNetworkData (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ)
    (schedule : List (ExchangeRequest n)) : NetworkData a s Omega n where
  sites := ⟨sites,fun _ => 0,phases⟩
  frame := 1
  origin := 0
  lo := lo
  hi := hi
  reference := lo
  region := Set.univ
  schedule := schedule
  clockResource := fun _ => true
  signalResource := fun _ => true
  relayResource := fun _ => true
  scalar := r
  metric := H

theorem populated_network_actual_sound (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ) (ordered : lo ≤ hi)
    (schedule : List (ExchangeRequest n)) :
    networkSound a s Omega n (populatedNetworkData a s Omega n r H sites phases lo hi schedule) := by
  refine ⟨?_,srNativeFrameComparisons.one_mem,ordered⟩
  intro i
  simpa [populatedNetworkData] using a.mass_pos

theorem inhabited_network_covers_every_old_preparation (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ) (ordered : lo ≤ hi)
    (schedule : List (ExchangeRequest n)) :
    ∃ receiver : LicensedNetworkReceiver a s Omega n, ∀ i : Fin (n+1),
      licensedSRScalar a s Omega (licensedNetworkToOld a s Omega n receiver i)=r ∧
      (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n receiver i)).metric=H := by
  let d := populatedNetworkData a s Omega n r H sites phases lo hi schedule
  let x : NetworkSource a s Omega n := ⟨d,fun _ => 0⟩
  refine ⟨presentLicensedNetwork a s Omega n x (populated_network_actual_sound a s Omega n r H sites phases lo hi ordered schedule),?_⟩
  intro i
  exact ⟨rfl,rfl⟩

end AASCKleinGordon.OperationalSR
