import OSRProperRebaseTransport
import OSRNetworkTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def licensedNetworkOperation (op : NetworkOperation n) (r : LicensedNetworkReceiver a s Omega n) :
    Option (LicensedNetworkReceiver a s Omega n) :=
  match step : networkOperation a s Omega n op (licensedNetworkSource a s Omega n r) with
  | none => none
  | some y => some (presentLicensedNetwork a s Omega n y
      (network_operation_preserves_actual_sound_region a s Omega n op _ y
        (licensed_network_has_actual_sound_source a s Omega n r) step))

theorem licensed_network_operation_actual_source_square (op : NetworkOperation n) (r : LicensedNetworkReceiver a s Omega n) :
    (licensedNetworkOperation a s Omega n op r).map (licensedNetworkSource a s Omega n)=
      networkOperation a s Omega n op (licensedNetworkSource a s Omega n r) := by
  unfold licensedNetworkOperation
  split <;> rename_i step <;> exact step.symm

def licensedNetworkObserve (r : LicensedNetworkReceiver a s Omega n) :=
  networkCompleteObserve a s Omega n (licensedNetworkSource a s Omega n r)

theorem licensed_network_operation_actual_readout_square (op : NetworkOperation n)
    (r : LicensedNetworkReceiver a s Omega n) (q : NetworkContext n) :
    (licensedNetworkOperation a s Omega n op r).map (fun next => licensedNetworkObserve a s Omega n next q)=
      (networkOperation a s Omega n op (licensedNetworkSource a s Omega n r)).map
        (fun next => networkCompleteObserve a s Omega n next q) := by
  rw [←licensed_network_operation_actual_source_square a s Omega n op r,Option.map_map]
  rfl

theorem licensed_network_operation_domain_is_exact (op : NetworkOperation n) (r : LicensedNetworkReceiver a s Omega n) :
    (licensedNetworkOperation a s Omega n op r).isSome=
      (networkOperation a s Omega n op (licensedNetworkSource a s Omega n r)).isSome := by
  have square := congrArg Option.isSome (licensed_network_operation_actual_source_square a s Omega n op r)
  simpa using square

def licensedNetworkFirstFailure : List (NetworkOperation n) → LicensedNetworkReceiver a s Omega n → Option ℕ
  | [],_ => none
  | op::ops,r => match licensedNetworkOperation a s Omega n op r with
    | none => some 0
    | some t => (licensedNetworkFirstFailure ops t).map Nat.succ

theorem licensed_network_full_finite_first_failure_square (ops : List (NetworkOperation n))
    (r : LicensedNetworkReceiver a s Omega n) :
    licensedNetworkFirstFailure a s Omega n ops r=networkFirstFailure a s Omega n ops (licensedNetworkSource a s Omega n r) := by
  induction ops generalizing r with
  | nil => rfl
  | cons op ops ih =>
    have square := licensed_network_operation_actual_source_square a s Omega n op r
    cases step : licensedNetworkOperation a s Omega n op r with
    | none =>
      simp only [step,Option.map_none] at square
      simp [licensedNetworkFirstFailure,step,networkFirstFailure,←square]
    | some t =>
      simp only [step,Option.map_some] at square
      simp [licensedNetworkFirstFailure,step,networkFirstFailure,←square,ih]

def licensedNetworkPassive (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n) : LicensedNetworkReceiver a s Omega n :=
  presentLicensedNetwork a s Omega n (passiveNetwork a s Omega n B c (licensedNetworkSource a s Omega n r))
    (passive_network_actually_sound a s Omega n B admitted c _
      (licensed_network_has_actual_sound_source a s Omega n r))

theorem licensed_network_passive_source_square (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n) :
    licensedNetworkSource a s Omega n (licensedNetworkPassive a s Omega n B admitted c r)=
      passiveNetwork a s Omega n B c (licensedNetworkSource a s Omega n r) := rfl

theorem licensed_network_passive_full_first_failure (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (ops : List (NetworkOperation n)) (r : LicensedNetworkReceiver a s Omega n) :
    licensedNetworkFirstFailure a s Omega n
      (ops.map (passiveNetworkOperation a s Omega n (licensedNetworkSource a s Omega n r).data))
      (licensedNetworkPassive a s Omega n B admitted c r)=licensedNetworkFirstFailure a s Omega n ops r := by
  rw [licensed_network_full_finite_first_failure_square,licensed_network_full_finite_first_failure_square]
  exact passive_network_finite_first_failure a s Omega n B c ops _

def selectedNetworkEvent (x : NetworkSource a s Omega n) (i : Fin (n+1)) : SREvent :=
  frameEvent x.data.frame x.data.origin (x.data.reference,x.data.sites.position i)

def selectedNetworkReading (x : NetworkSource a s Omega n) (i : Fin (n+1)) : ℝ :=
  siteReading a.mass x.data.sites i x.data.reference

theorem selected_network_event_and_reading_are_actual (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) :
    let time := srPassiveMarkedTime a.mass x.data.frame x.data.origin (siteRecord a.mass x.data.sites i) x.data.reference
    srMarkedClockEvent a.mass (networkRawJoint a s Omega n x i).clock.record time=selectedNetworkEvent a s Omega n x i ∧
    (srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record time).2.reading=
      selectedNetworkReading a s Omega n x i := by
  dsimp only
  have records := network_raw_record_is_same_marked_history a s Omega n x i
    (srPassiveMarkedTime a.mass x.data.frame x.data.origin (siteRecord a.mass x.data.sites i) x.data.reference)
  constructor
  · change (_, (srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record _).2.position)=_
    rw [records]
    exact raw_network_clock_actual_same_event a s Omega n x.data sound i _
  · rw [records]
    exact raw_network_clock_actual_same_reading a s Omega n x.data sound i _

theorem actual_reference_advance_selected_event_and_reading (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) (delta : ℝ) (forward : 0 ≤ delta) :
    let y : NetworkSource a s Omega n := {x with data := {x.data with reference := x.data.reference+delta}}
    selectedNetworkEvent a s Omega n y i=frameEvent x.data.frame x.data.origin
      (x.data.reference+delta,x.data.sites.position i) ∧
    selectedNetworkReading a s Omega n y i=x.data.sites.phase i+x.data.reference+delta ∧
    networkOperation a s Omega n (.advance delta) x=some y := by
  dsimp only
  refine ⟨rfl,?_,network_nonnegative_reference_advance_is_actual a s Omega n x delta forward⟩
  rw [selectedNetworkReading,siteReading,site_actual_reading a.mass x.data.sites i (sound.1 i)]
  ring

end AASCKleinGordon.OperationalSR
