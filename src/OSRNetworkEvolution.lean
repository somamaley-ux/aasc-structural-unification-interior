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

theorem network_data_operation_retains_actual_records (op : NetworkOperation n)
    (d e : NetworkData a s Omega n) (step : networkDataOperation a s Omega n op d=some e) (i : Fin (n+1)) :
    (networkBaseJoint a s Omega n e i).clock.record=(networkBaseJoint a s Omega n d i).clock.record := by
  cases op <;> simp only [networkDataOperation] at step
  all_goals first | (cases step; rfl) | (split_ifs at step <;> cases step <;> rfl)

theorem network_raw_record_is_same_marked_history (x : NetworkSource a s Omega n) (i : Fin (n+1)) (t : ℝ) :
    srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record t=
      srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n x.data i).clock.record t :=
  joint_clock_rebase_preserves_all_marked_records a s Omega (observerSlope x.data.frame*x.epoch i) t (networkBaseJoint a s Omega n x.data i)

theorem network_all_successful_operations_retain_underlying_histories (op : NetworkOperation n)
    (x y : NetworkSource a s Omega n) (step : networkOperation a s Omega n op x=some y)
    (i : Fin (n+1)) (t : ℝ) :
    srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n y i).clock.record t=
      srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record t := by
  rw [network_raw_record_is_same_marked_history,network_raw_record_is_same_marked_history]
  have dataStep := network_operation_actual_data_square a s Omega n op x
  rw [step,Option.map_some] at dataStep
  rw [network_data_operation_retains_actual_records a s Omega n op x.data y.data dataStep.symm i]

theorem site_window_extension_is_actual_old_extension (mu0 : ℝ) {k : ℕ} (S : SiteData k)
    (i : Fin (k+1)) (positive : 0 < mu0+S.internalEnergy i) (lo hi delta : ℝ) :
    siteUse mu0 S i lo (hi+delta)=srNativeExtendClockUse mu0 delta (siteUse mu0 S i lo hi) := by
  apply sr_clock_use_ext
  · rfl
  · rfl
  · rfl
  · change hi+delta-lo=srNativeClockActualInterval mu0 (srNativeExtendClockUse mu0 delta (siteUse mu0 S i lo hi))
    change hi+delta-lo=siteReading mu0 S i (hi+delta)-siteReading mu0 S i lo
    rw [siteReading,siteReading,site_actual_reading mu0 S i positive,site_actual_reading mu0 S i positive]
    ring

theorem network_window_extension_has_actual_coordinate_slope (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (delta : ℝ) :
    (networkBaseJoint a s Omega n {d with hi := d.hi+delta} i).clock=
      srNativeExtendClockUse a.mass
        (srPassiveClockSlope a.mass d.frame (siteRecord a.mass d.sites i).2.2*delta)
        (networkBaseJoint a s Omega n d i).clock := by
  change srPassiveClockUse a.mass d.frame d.origin (siteUse a.mass d.sites i d.lo (d.hi+delta))=_
  rw [site_window_extension_is_actual_old_extension a.mass d.sites i (sound.1 i)]
  exact sr_passive_clock_use_extension a.mass a.mass_pos (srNativeOccupiedFrameSource a.mass a.mass_pos)
    d.frame sound.2.1 d.origin _ delta (sound.1 i)

theorem network_nonnegative_reference_advance_is_actual (x : NetworkSource a s Omega n) (delta : ℝ)
    (forward : 0 ≤ delta) :
    networkOperation a s Omega n (.advance delta) x=some {x with data := {x.data with reference := x.data.reference+delta}} := by
  simp [networkOperation,networkDataOperation,forward]

theorem network_continuation_selection_exit_is_retained (x : NetworkSource a s Omega n) (delta : ℝ)
    (forward : 0 ≤ delta) (exit : x.data.hi < x.data.reference+delta) :
    networkCompleteObserve a s Omega n x (.domain (.advance delta))=true ∧
    networkCompleteObserve a s Omega n x (.after (.advance delta) (.original .referenceSelection))=
      some (x.data.reference+delta,false) := by
  simp [networkCompleteObserve,srCompleteOriginalContextObserve,network_nonnegative_reference_advance_is_actual,
    forward,networkOriginalObserve,networkDataObserve,show ¬ (x.data.reference+delta ≤ x.data.hi) from not_le.mpr exit]

def networkReceiverOperation (op : NetworkOperation n) : NetworkReceiver a s Omega n → Option (NetworkReceiver a s Omega n) :=
  Classical.choose (network_all_registered_operations_have_exact_descent a s Omega n op)

theorem network_receiver_operation_square (op : NetworkOperation n) (x : NetworkSource a s Omega n) :
    networkReceiverOperation a s Omega n op (presentNetwork a s Omega n x)=
      (networkOperation a s Omega n op x).map (presentNetwork a s Omega n) :=
  (Classical.choose_spec (network_all_registered_operations_have_exact_descent a s Omega n op)).1 x

def networkFirstFailure : List (NetworkOperation n) → NetworkSource a s Omega n → Option ℕ
  | [],_ => none
  | op::ops,x => match networkOperation a s Omega n op x with
    | none => some 0
    | some y => (networkFirstFailure ops y).map Nat.succ

def networkReceiverFirstFailure : List (NetworkOperation n) → NetworkReceiver a s Omega n → Option ℕ
  | [],_ => none
  | op::ops,x => match networkReceiverOperation a s Omega n op x with
    | none => some 0
    | some y => (networkReceiverFirstFailure ops y).map Nat.succ

theorem network_finite_first_failure_square (ops : List (NetworkOperation n)) (x : NetworkSource a s Omega n) :
    networkReceiverFirstFailure a s Omega n ops (presentNetwork a s Omega n x)=networkFirstFailure a s Omega n ops x := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    simp only [networkReceiverFirstFailure,network_receiver_operation_square]
    cases step : networkOperation a s Omega n op x with
    | none => simp [networkFirstFailure,step]
    | some y => simp [networkFirstFailure,step,ih]

theorem licensed_network_same_metric_operand (r : LicensedNetworkReceiver a s Omega n)
    (i : Fin (n+1)) (kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    restrictedEHMetric a s Omega (licensedEHResponse a s Omega (licensedSRMetric a s Omega kappa Lambda coupling
      (licensedNetworkToOld a s Omega n r i)))=originalEHActMetric (licensedNetworkSource a s Omega n r).data.metric.val :=
  licensed_sr_same_metric_operand_square a s Omega kappa Lambda coupling _

theorem licensed_network_complete_registered_reference (r : LicensedNetworkReceiver a s Omega n)
    (i : Fin (n+1)) (kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (q : RegisteredQuestion (KGFamilyQuestion a Omega (kgOriginalObject a))) :
    (licensedReadout a s Omega (licensedSRMetric a s Omega kappa Lambda coupling (licensedNetworkToOld a s Omega n r i)) []).answer
      (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q))=
    (licensedScalarReference a s Omega (scalarBaseObject a) (licensedNetworkSource a s Omega n r).data.scalar
      (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr :=
  licensed_sr_complete_registered_reference_square a s Omega kappa Lambda coupling _ q

end AASCKleinGordon.OperationalSR
