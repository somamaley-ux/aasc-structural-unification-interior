import OriginalPreparedRestoration
import KernelReference.ContextualQuotient

/-! A concrete contextual receiver for histories generated from the existing
original prepared carrier. It covers exactly the displayed registered-observe,
admitted-operand-variation and frame repertoire. No field asserts that this
repertoire exhausts the original gravity role or all original joint processes.
All history and operation congruence below is derived from the constructors. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
open AASC.KernelReference.ContextualQuotient
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

structure PreparedHistoryProfile where
  source : PreparedOriginal a s Ω
  target : PreparedOriginal a s Ω
  events : List (PreparedEvent a s Ω)

def preparedHistoryProfile (x : PreparedHistoryState a s Ω) : PreparedHistoryProfile a s Ω :=
  ⟨x.source,preparedOriginalBase a s Ω x.locus,x.events⟩

theorem prepared_history_profile_eq_iff (x y : PreparedHistoryState a s Ω) :
    preparedHistoryProfile a s Ω x = preparedHistoryProfile a s Ω y ↔
      PreparedHistorySame a s Ω x y := by
  constructor
  · intro same
    exact ⟨congrArg PreparedHistoryProfile.source same,congrArg PreparedHistoryProfile.target same,
      congrArg PreparedHistoryProfile.events same⟩
  · rintro ⟨source,base,events⟩
    unfold preparedHistoryProfile
    rw [source,base,events]

/-- Inputs are actual old carriers and operation syntax; no purported ledger,
answer, role-preservation or coverage certificate is supplied. -/
structure PreparedOriginalHistory where
  initial : PreparedLocus a s Ω
  program : List (PreparedHistoryOperation a Ω)

def preparedOriginalHistoryRun (h : PreparedOriginalHistory a s Ω) : PreparedHistoryState a s Ω :=
  preparedHistoryRun a s Ω h.program (preparedHistoryInitial a s Ω h.initial)

def preparedOriginalHistoryAppend (h : PreparedOriginalHistory a s Ω)
    (operations : List (PreparedHistoryOperation a Ω)) : PreparedOriginalHistory a s Ω :=
  ⟨h.initial,h.program++operations⟩

theorem prepared_original_history_append_run (h : PreparedOriginalHistory a s Ω)
    (operations : List (PreparedHistoryOperation a Ω)) :
    preparedOriginalHistoryRun a s Ω (preparedOriginalHistoryAppend a s Ω h operations) =
      preparedHistoryRun a s Ω operations (preparedOriginalHistoryRun a s Ω h) :=
  prepared_history_run_append a s Ω h.program operations _

def preparedOriginalHistoryEvaluate (h : PreparedOriginalHistory a s Ω)
    (continuation : List (PreparedHistoryOperation a Ω)) : PreparedHistoryProfile a s Ω :=
  preparedHistoryProfile a s Ω
    (preparedHistoryRun a s Ω continuation (preparedOriginalHistoryRun a s Ω h))

abbrev PreparedHistoryEquivalent (x y : PreparedOriginalHistory a s Ω) :=
  Equivalent (preparedOriginalHistoryEvaluate a s Ω) x y

theorem prepared_history_context_equivalence_iff (x y : PreparedOriginalHistory a s Ω) :
    PreparedHistoryEquivalent a s Ω x y ↔
      PreparedHistorySame a s Ω (preparedOriginalHistoryRun a s Ω x)
        (preparedOriginalHistoryRun a s Ω y) := by
  constructor
  · intro same
    exact (prepared_history_profile_eq_iff a s Ω _ _).mp (same [])
  · intro same continuation
    exact (prepared_history_profile_eq_iff a s Ω _ _).mpr
      (prepared_history_run_congruence a s Ω continuation _ _ same)

theorem prepared_history_append_evaluation (h : PreparedOriginalHistory a s Ω)
    (operations continuation : List (PreparedHistoryOperation a Ω)) :
    preparedOriginalHistoryEvaluate a s Ω (preparedOriginalHistoryAppend a s Ω h operations) continuation =
      preparedOriginalHistoryEvaluate a s Ω h (operations++continuation) := by
  unfold preparedOriginalHistoryEvaluate
  rw [prepared_original_history_append_run,prepared_history_run_append]

theorem prepared_history_append_congruence (operations : List (PreparedHistoryOperation a Ω))
    (x y : PreparedOriginalHistory a s Ω) (same : PreparedHistoryEquivalent a s Ω x y) :
    PreparedHistoryEquivalent a s Ω (preparedOriginalHistoryAppend a s Ω x operations)
      (preparedOriginalHistoryAppend a s Ω y operations) := by
  intro continuation
  rw [prepared_history_append_evaluation,prepared_history_append_evaluation]
  exact same (operations++continuation)

abbrev PreparedHistoryReceiver := CanonicalQuotient (preparedOriginalHistoryEvaluate a s Ω)

def preparedHistoryReceive (h : PreparedOriginalHistory a s Ω) : PreparedHistoryReceiver a s Ω :=
  classify (preparedOriginalHistoryEvaluate a s Ω) h

theorem prepared_history_receive_eq_iff (x y : PreparedOriginalHistory a s Ω) :
    preparedHistoryReceive a s Ω x = preparedHistoryReceive a s Ω y ↔
      PreparedHistorySame a s Ω (preparedOriginalHistoryRun a s Ω x)
        (preparedOriginalHistoryRun a s Ω y) :=
  (classify_eq_iff _ x y).trans (prepared_history_context_equivalence_iff a s Ω x y)

def preparedHistoryReadProfile : PreparedHistoryReceiver a s Ω → PreparedHistoryProfile a s Ω :=
  readCoordinate (preparedOriginalHistoryEvaluate a s Ω) []

theorem prepared_history_read_profile_square (h : PreparedOriginalHistory a s Ω) :
    preparedHistoryReadProfile a s Ω (preparedHistoryReceive a s Ω h) =
      preparedHistoryProfile a s Ω (preparedOriginalHistoryRun a s Ω h) := rfl

def preparedHistoryContinue (operations : List (PreparedHistoryOperation a Ω)) :
    PreparedHistoryReceiver a s Ω → PreparedHistoryReceiver a s Ω :=
  Quotient.lift (fun h => preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h operations))
    (fun x y same => (classify_eq_iff _ _ _).mpr
      (prepared_history_append_congruence a s Ω operations x y same))

theorem prepared_history_continuation_square (operations : List (PreparedHistoryOperation a Ω))
    (h : PreparedOriginalHistory a s Ω) :
    preparedHistoryContinue a s Ω operations (preparedHistoryReceive a s Ω h) =
      preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h operations) := rfl

theorem prepared_history_continuation_unique (operations : List (PreparedHistoryOperation a Ω)) :
    ∃! f : PreparedHistoryReceiver a s Ω → PreparedHistoryReceiver a s Ω,
      ∀ h,f (preparedHistoryReceive a s Ω h) =
        preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h operations) :=
  unique_factorization (preparedOriginalHistoryEvaluate a s Ω) _
    (fun x y same => (classify_eq_iff _ _ _).mpr
      (prepared_history_append_congruence a s Ω operations x y same))

theorem prepared_history_continuation_identity (q : PreparedHistoryReceiver a s Ω) :
    preparedHistoryContinue a s Ω [] q = q := by
  induction q using Quotient.inductionOn with
  | _ h =>
    change preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h []) =
      preparedHistoryReceive a s Ω h
    have empty : preparedOriginalHistoryAppend a s Ω h [] = h := by
      cases h
      simp [preparedOriginalHistoryAppend]
    rw [empty]

theorem prepared_history_continuation_composition (first second : List (PreparedHistoryOperation a Ω))
    (q : PreparedHistoryReceiver a s Ω) :
    preparedHistoryContinue a s Ω second (preparedHistoryContinue a s Ω first q) =
      preparedHistoryContinue a s Ω (first++second) q := by
  induction q using Quotient.inductionOn with
  | _ h =>
    change preparedHistoryReceive a s Ω
      (preparedOriginalHistoryAppend a s Ω (preparedOriginalHistoryAppend a s Ω h first) second) =
        preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h (first++second))
    congr 1
    cases h
    simp [preparedOriginalHistoryAppend,List.append_assoc]

def preparedHistoryReference (q : PreparedHistoryReceiver a s Ω) (π : PreparedQuestion a Ω) :
    Option KGPreparedReadout :=
  kgJointFrameOriginalAnswer s Ω (kgOriginalObject a) (preparedHistoryReadProfile a s Ω q).target π

theorem prepared_history_original_reference_square (h : PreparedOriginalHistory a s Ω)
    (π : PreparedQuestion a Ω) :
    preparedHistoryReference a s Ω (preparedHistoryReceive a s Ω h) π =
      (kgJointFrameFamilyReferences s Ω (kgOriginalObject a)).referenceAt
        (preparedOriginalHistoryRun a s Ω h).locus π :=
  prepared_event_answer_at_frame a s Ω _ π

def preparedHistoryEHReadout (κ Λ : ℝ) (q : PreparedHistoryReceiver a s Ω) : Option ℝ :=
  (originalEHPreparedUse s Ω (kgOriginalObject a) κ Λ (preparedHistoryReadProfile a s Ω q).target).2

theorem prepared_history_eh_readout_square (κ Λ : ℝ) (h : PreparedOriginalHistory a s Ω) :
    preparedHistoryEHReadout a s Ω κ Λ (preparedHistoryReceive a s Ω h) =
      (originalEHJointFrameUse s Ω (kgOriginalObject a) κ Λ
        (preparedOriginalHistoryRun a s Ω h).locus.1 (preparedOriginalHistoryRun a s Ω h).locus.2).2 := by
  have hframe := original_eh_joint_frame_evaluator s Ω (kgOriginalObject a) κ Λ
    (preparedOriginalHistoryRun a s Ω h).locus.1
    (preparedOriginalBase a s Ω (preparedOriginalHistoryRun a s Ω h).locus)
  simpa only [preparedOriginalBase,originalEHJointFrameOriginal,Equiv.apply_symm_apply] using hframe.symm

def preparedHistoryReadFirstFailure (q : PreparedHistoryReceiver a s Ω) : Option (ℕ × KGExecutionFailure) :=
  preparedHistoryFirstFailure a s Ω (preparedHistoryReadProfile a s Ω q).events

theorem prepared_history_first_failure_square (h : PreparedOriginalHistory a s Ω) :
    preparedHistoryReadFirstFailure a s Ω (preparedHistoryReceive a s Ω h) =
      preparedHistoryFirstFailure a s Ω (preparedOriginalHistoryRun a s Ω h).events := rfl

theorem prepared_history_quotient_first_failure_retained (operations : List (PreparedHistoryOperation a Ω))
    (q : PreparedHistoryReceiver a s Ω) (n : ℕ) (reason : KGExecutionFailure)
    (failed : preparedHistoryReadFirstFailure a s Ω q = some (n,reason)) :
    preparedHistoryReadFirstFailure a s Ω (preparedHistoryContinue a s Ω operations q) = some (n,reason) := by
  induction q using Quotient.inductionOn with
  | _ h =>
    change preparedHistoryFirstFailure a s Ω
      (preparedOriginalHistoryRun a s Ω (preparedOriginalHistoryAppend a s Ω h operations)).events = _
    rw [prepared_original_history_append_run]
    exact prepared_history_first_failure_retained a s Ω operations _ n reason failed

theorem prepared_history_frame_is_redescription (q : ProperPoincareTransform)
    (h : PreparedOriginalHistory a s Ω) :
    preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h [.frame q]) =
      preparedHistoryReceive a s Ω h := by
  apply (prepared_history_receive_eq_iff a s Ω _ _).mpr
  rw [prepared_original_history_append_run]
  exact prepared_history_frame_same a s Ω q _

theorem prepared_history_metric_restore_keeps_distinct_history (K : MetricSourceProbe Ω)
    (h : PreparedOriginalHistory a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω (preparedOriginalHistoryRun a s Ω h).locus)).val+K ∈
        wickOriginalMetricNeighborhood Ω) :
    preparedOriginalBase a s Ω (preparedOriginalHistoryRun a s Ω
      (preparedOriginalHistoryAppend a s Ω h [.vary K,.vary (-K)])).locus =
        preparedOriginalBase a s Ω (preparedOriginalHistoryRun a s Ω h).locus ∧
    preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h [.vary K,.vary (-K)]) ≠
      preparedHistoryReceive a s Ω h := by
  constructor
  · rw [prepared_original_history_append_run]
    exact prepared_history_restore_base a s Ω K _ inside
  · intro same
    have records := (prepared_history_receive_eq_iff a s Ω _ _).mp same
    rw [prepared_original_history_append_run] at records
    exact prepared_history_restoration_is_not_history_erasure a s Ω K _ records

end
end AASCKleinGordon
