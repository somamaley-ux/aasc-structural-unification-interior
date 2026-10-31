import SRJointOriginalSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace AASCMetricConstruction
open AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem joint_clock_rebase_add (h k : ℝ) (j : JointOriginalSource a s Ω) :
    jointClockRebase a s Ω h (jointClockRebase a s Ω k j) =
      jointClockRebase a s Ω (h+k) j := by
  cases j
  simp [jointClockRebase,srNativeClockUseRedescription,srNativeClockRedescription,
    sr_native_coasting_flow_composition,add_comm,add_left_comm]

theorem joint_clock_rebase_commutes (h k : ℝ) (j : JointOriginalSource a s Ω) :
    jointClockRebase a s Ω h (jointClockRebase a s Ω k j) =
      jointClockRebase a s Ω k (jointClockRebase a s Ω h j) := by
  rw [joint_clock_rebase_add,joint_clock_rebase_add,add_comm h k]

theorem joint_clock_rebase_original_observe (h : ℝ) (j : JointOriginalSource a s Ω)
    (q : JointQuestion) :
    jointOriginalObserve a s Ω (jointClockRebase a s Ω h j) q =
      jointOriginalObserve a s Ω j q := by
  cases q with
  | inl t => exact joint_clock_rebase_preserves_all_marked_records a s Ω h t j
  | inr q => cases q <;> rfl

theorem joint_clock_rebase_operation_naturality (h : ℝ) (op : JointOperation)
    (j : JointOriginalSource a s Ω) :
    jointOperation a s Ω op (jointClockRebase a s Ω h j) =
      (jointOperation a s Ω op j).map (jointClockRebase a s Ω h) := by
  cases op with
  | clockRebase k =>
    simp only [jointOperation,Option.map_some]
    exact congrArg some (joint_clock_rebase_commutes a s Ω k h j)
  | scalarContinue t => rfl
  | clockExtend δ =>
    simp only [jointOperation]
    split
    · simp only [Option.map_some]
      congr 1
      cases j
      simp only [jointClockExtend,jointClockRebase]
      rw [AASCMetricConstruction.SRIntegration.sr_native_clock_rebase_extension_commutes]
    · rfl
  | certifyClockInterval =>
    simp only [jointOperation,joint_clock_rebase_preserves_validity]
    split <;> rfl

theorem joint_clock_rebase_complete_context_profile (h : ℝ) (j : JointOriginalSource a s Ω) :
    jointCompleteObserve a s Ω (jointClockRebase a s Ω h j) = jointCompleteObserve a s Ω j := by
  funext q
  induction q generalizing j with
  | original q => exact joint_clock_rebase_original_observe a s Ω h j q
  | domain op =>
    change (jointOperation a s Ω op (jointClockRebase a s Ω h j)).isSome = _
    rw [joint_clock_rebase_operation_naturality]
    simp [jointCompleteObserve,srCompleteOriginalContextObserve]
  | after op q ih =>
    change (jointOperation a s Ω op (jointClockRebase a s Ω h j)).map
      (fun x => jointCompleteObserve a s Ω x q) = _
    rw [joint_clock_rebase_operation_naturality,Option.map_map]
    congr 1
    funext x
    exact ih x

theorem joint_clock_rebase_receiver_square (h : ℝ) (j : JointOriginalSource a s Ω) :
    presentJointOriginal a s Ω (jointClockRebase a s Ω h j) = presentJointOriginal a s Ω j := by
  apply (ContextualQuotient.classify_eq_iff _ _ _).mpr
  intro q
  exact congrFun (joint_clock_rebase_complete_context_profile a s Ω h j) q

def jointReceiverOperation (op : JointOperation) : JointReceiver a s Ω → Option (JointReceiver a s Ω) :=
  Classical.choose (joint_registered_operations_have_unique_exact_descent a s Ω op)

theorem joint_receiver_operation_square (op : JointOperation) (j : JointOriginalSource a s Ω) :
    jointReceiverOperation a s Ω op (presentJointOriginal a s Ω j) =
      (jointOperation a s Ω op j).map (presentJointOriginal a s Ω) :=
  (Classical.choose_spec (joint_registered_operations_have_unique_exact_descent a s Ω op)).1 j

def jointFirstFailure : List JointOperation → JointOriginalSource a s Ω → Option ℕ
  | [], _ => none
  | op::ops, j => match jointOperation a s Ω op j with
    | none => some 0
    | some k => (jointFirstFailure ops k).map Nat.succ

def jointReceiverFirstFailure : List JointOperation → JointReceiver a s Ω → Option ℕ
  | [], _ => none
  | op::ops, j => match jointReceiverOperation a s Ω op j with
    | none => some 0
    | some k => (jointReceiverFirstFailure ops k).map Nat.succ

theorem joint_first_failure_square (ops : List JointOperation) (j : JointOriginalSource a s Ω) :
    jointReceiverFirstFailure a s Ω ops (presentJointOriginal a s Ω j) =
      jointFirstFailure a s Ω ops j := by
  induction ops generalizing j with
  | nil => rfl
  | cons op ops ih =>
    simp only [jointReceiverFirstFailure,joint_receiver_operation_square]
    cases he : jointOperation a s Ω op j with
    | none => simp [jointFirstFailure,he]
    | some k => simp [jointFirstFailure,he,ih]

theorem joint_old_receiver_preparation_coverage :
    Function.Surjective (jointReceiverOldPreparation a s Ω) := by
  rintro ⟨r,H⟩
  obtain ⟨j,_,hj⟩ := joint_source_covers_every_old_preparation a s Ω r H
  exact ⟨presentJointOriginal a s Ω j,hj⟩

#print axioms joint_clock_rebase_complete_context_profile
#print axioms joint_first_failure_square
#print axioms joint_old_receiver_preparation_coverage
end AASCKleinGordon.CanonicalLicensing.SRIntegration
