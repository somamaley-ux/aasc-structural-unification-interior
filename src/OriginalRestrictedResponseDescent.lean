import OriginalRestrictedRawExecution

/-! Retained original-source comparison and response descent for the existing
KG program restriction. Coverage lifts actual quotient preparations objectwise.
No minimality of raw storage, universal R2 coverage, or profile agreement field
is an input. Successful extra occurrences are retained as source records; their
further R2 significance is not decided by this construction. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def restrictedRawHistoryReceive (h : RestrictedRawHistory a Ω) : PreparedHistoryReceiver a s Ω :=
  preparedHistoryReceive a s Ω (restrictedRawHistoryPresent a s Ω h)

theorem restricted_raw_history_receive_surjective :
    Function.Surjective (restrictedRawHistoryReceive a s Ω) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ h =>
    obtain ⟨x, hx⟩ := restricted_raw_history_covers_prepared_histories a s Ω h
    exact ⟨x, congrArg (preparedHistoryReceive a s Ω) hx⟩

def RestrictedRawStateSame (x y : RestrictedRawState a Ω) : Prop :=
  RestrictedRawSame a s Ω x.source y.source ∧
    RestrictedRawSame a s Ω x.current y.current ∧
    List.Forall₂ (RestrictedRawEventSame a s Ω) x.events y.events

def RestrictedRawProgramSame (h k : RestrictedRawHistory a Ω) : Prop :=
  RestrictedRawStateSame a s Ω (restrictedRawHistoryRun a Ω h) (restrictedRawHistoryRun a Ω k)

theorem restricted_raw_events_comparison_exact (es fs : List (RestrictedRawEvent a Ω)) :
    es.map (restrictedRawEventReceive a s Ω) = fs.map (restrictedRawEventReceive a s Ω) ↔
      List.Forall₂ (RestrictedRawEventSame a s Ω) es fs := by
  induction es generalizing fs with
  | nil => cases fs <;> simp
  | cons e es ih =>
    cases fs with
    | nil => simp
    | cons f fs =>
      constructor
      · intro same
        have parts := List.cons.inj same
        exact .cons ((restricted_raw_event_comparison_exact a s Ω e f).mp parts.1)
          ((ih fs).mp parts.2)
      · intro same
        cases same with
        | cons head tail =>
          exact congrArg₂ List.cons
            ((restricted_raw_event_comparison_exact a s Ω e f).mpr head) ((ih fs).mpr tail)

theorem restricted_raw_state_comparison_exact (x y : RestrictedRawState a Ω) :
    RestrictedRawStateSame a s Ω x y ↔
      restrictedRawReceive a s Ω x.source = restrictedRawReceive a s Ω y.source ∧
      restrictedRawReceive a s Ω x.current = restrictedRawReceive a s Ω y.current ∧
      x.events.map (restrictedRawEventReceive a s Ω) = y.events.map (restrictedRawEventReceive a s Ω) := by
  unfold RestrictedRawStateSame
  rw [← restricted_raw_receive_eq_iff, ← restricted_raw_receive_eq_iff,
    ← restricted_raw_events_comparison_exact]

theorem restricted_original_response_comparison_exact (h k : RestrictedRawHistory a Ω) :
    RestrictedRawProgramSame a s Ω h k ↔
      restrictedRawHistoryReceive a s Ω h = restrictedRawHistoryReceive a s Ω k := by
  have left := restricted_raw_history_run_matches a s Ω h
  have right := restricted_raw_history_run_matches a s Ω k
  unfold RestrictedRawProgramSame
  rw [restricted_raw_state_comparison_exact]
  rw [left.1, right.1, left.2.1, right.2.1, left.2.2, right.2.2]
  exact (prepared_history_receive_eq_iff a s Ω _ _).symm

theorem restricted_original_comparison_preserved_by_context
    (h k : RestrictedRawHistory a Ω) (same : RestrictedRawProgramSame a s Ω h k)
    (ops : List (PreparedHistoryOperation a Ω)) :
    RestrictedRawProgramSame a s Ω (restrictedRawHistoryAppend a Ω h ops)
      (restrictedRawHistoryAppend a Ω k ops) := by
  apply (restricted_original_response_comparison_exact a s Ω _ _).mpr
  have mapped := congrArg (preparedHistoryContinue a s Ω ops)
    ((restricted_original_response_comparison_exact a s Ω h k).mp same)
  exact mapped

theorem restricted_original_context_comparison_exact (h k : RestrictedRawHistory a Ω) :
    RestrictedRawProgramSame a s Ω h k ↔
      ∀ ops, RestrictedRawProgramSame a s Ω (restrictedRawHistoryAppend a Ω h ops)
        (restrictedRawHistoryAppend a Ω k ops) := by
  constructor
  · exact restricted_original_comparison_preserved_by_context a s Ω h k
  · intro all
    simpa only [restrictedRawHistoryAppend, List.append_nil] using all []

theorem restricted_original_current_answer_readback (h : RestrictedRawHistory a Ω)
    (π : PreparedQuestion a Ω) :
    restrictedRawAnswer a s Ω (restrictedRawHistoryRun a Ω h).current π =
      preparedHistoryReference a s Ω (restrictedRawHistoryReceive a s Ω h) π := by
  rw [restricted_raw_answer_square]
  change kgJointFrameOriginalAnswer s Ω (kgOriginalObject a)
      (restrictedRawReceive a s Ω (restrictedRawHistoryRun a Ω h).current) π = _
  rw [(restricted_raw_history_run_matches a s Ω h).2.1]
  rfl

def restrictedRawFirstFailure : List (RestrictedRawEvent a Ω) → Option (ℕ × KGExecutionFailure)
  | [] => none
  | e :: rest => match restrictedRawFailure a s Ω e.origin e.question with
    | some reason => some (0, reason)
    | none => (restrictedRawFirstFailure rest).map (fun p => (p.1 + 1, p.2))

theorem restricted_raw_first_failure_readback (events : List (RestrictedRawEvent a Ω)) :
    restrictedRawFirstFailure a s Ω events =
      preparedHistoryFirstFailure a s Ω (events.map (restrictedRawEventReceive a s Ω)) := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    simp only [restrictedRawFirstFailure, List.map_cons, preparedHistoryFirstFailure,
      restrictedRawEventReceive, ← restricted_raw_failure_square, ih]
    rfl

theorem restricted_original_failure_readback (h : RestrictedRawHistory a Ω) :
    restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω h).events =
      preparedHistoryReadFirstFailure a s Ω (restrictedRawHistoryReceive a s Ω h) := by
  rw [restricted_raw_first_failure_readback, (restricted_raw_history_run_matches a s Ω h).2.2]
  rfl

def restrictedRawOperationFailure (op : PreparedHistoryOperation a Ω) (x : RestrictedRaw a Ω) :
    Option KGExecutionFailure :=
  match op with
  | .observe π => restrictedRawFailure a s Ω x π
  | .frame _ => none
  | .vary K => restrictedRawFailure a s Ω x (preparedFiniteRequest a Ω (x.act.val + K))

theorem restricted_raw_operation_failure_square (op : PreparedHistoryOperation a Ω)
    (x : RestrictedRaw a Ω) :
    restrictedRawOperationFailure a s Ω op x =
      preparedOriginalOperationFailure a s Ω op (restrictedRawReceive a s Ω x) := by
  cases op with
  | observe π => exact restricted_raw_failure_square a s Ω x π
  | frame _ => rfl
  | vary K => exact restricted_raw_failure_square a s Ω x (preparedFiniteRequest a Ω (x.act.val + K))

theorem restricted_original_operation_diagnostic_readback (op : PreparedHistoryOperation a Ω)
    (h : RestrictedRawHistory a Ω) :
    restrictedRawOperationFailure a s Ω op (restrictedRawHistoryRun a Ω h).current =
      preparedOriginalOperationFailure a s Ω op
        (preparedExecutionProjection a s Ω (restrictedRawHistoryReceive a s Ω h)) := by
  rw [restricted_raw_operation_failure_square, (restricted_raw_history_run_matches a s Ω h).2.1]
  rfl

/-- Admission of the next original use, not reclassification of earlier failures. -/
def restrictedRawPartialAppend (op : PreparedHistoryOperation a Ω) (h : RestrictedRawHistory a Ω) :
    Option (RestrictedRawHistory a Ω) :=
  if restrictedRawOperationFailure a s Ω op (restrictedRawHistoryRun a Ω h).current = none then
    some (restrictedRawHistoryAppend a Ω h [op]) else none

theorem restricted_original_partial_operation_readback (op : PreparedHistoryOperation a Ω)
    (h : RestrictedRawHistory a Ω) :
    (restrictedRawPartialAppend a s Ω op h).map (restrictedRawHistoryReceive a s Ω) =
      preparedExecutionPartialOperation a s Ω op (restrictedRawHistoryReceive a s Ω h) := by
  unfold restrictedRawPartialAppend preparedExecutionPartialOperation
  rw [restricted_original_operation_diagnostic_readback]
  split <;> rfl

def restrictedOriginalResponseSetoid : Setoid (RestrictedRawHistory a Ω) where
  r := RestrictedRawProgramSame a s Ω
  iseqv := ⟨
    fun h => (restricted_original_response_comparison_exact a s Ω h h).mpr rfl,
    fun same => (restricted_original_response_comparison_exact a s Ω _ _).mpr
      ((restricted_original_response_comparison_exact a s Ω _ _).mp same).symm,
    fun first second => (restricted_original_response_comparison_exact a s Ω _ _).mpr
      (((restricted_original_response_comparison_exact a s Ω _ _).mp first).trans
        ((restricted_original_response_comparison_exact a s Ω _ _).mp second))⟩

abbrev RestrictedOriginalResponse := Quotient (restrictedOriginalResponseSetoid a s Ω)

def restrictedOriginalResponseReceive : RestrictedOriginalResponse a s Ω → PreparedHistoryReceiver a s Ω :=
  Quotient.lift (restrictedRawHistoryReceive a s Ω)
    (fun h k same => (restricted_original_response_comparison_exact a s Ω h k).mp same)

theorem restricted_original_response_receive_bijective :
    Function.Bijective (restrictedOriginalResponseReceive a s Ω) := by
  constructor
  · intro x y same
    induction x using Quotient.inductionOn with
    | _ h =>
      induction y using Quotient.inductionOn with
      | _ k =>
        exact Quotient.sound ((restricted_original_response_comparison_exact a s Ω h k).mpr same)
  · intro q
    obtain ⟨h, same⟩ := restricted_raw_history_receive_surjective a s Ω q
    exact ⟨Quotient.mk _ h, same⟩

def restrictedOriginalResponseContinue (ops : List (PreparedHistoryOperation a Ω)) :
    RestrictedOriginalResponse a s Ω → RestrictedOriginalResponse a s Ω :=
  Quotient.lift (fun h => Quotient.mk _ (restrictedRawHistoryAppend a Ω h ops))
    (fun h k same => Quotient.sound (restricted_original_comparison_preserved_by_context a s Ω h k same ops))

theorem restricted_original_response_continuation_square (ops : List (PreparedHistoryOperation a Ω))
    (q : RestrictedOriginalResponse a s Ω) :
    restrictedOriginalResponseReceive a s Ω (restrictedOriginalResponseContinue a s Ω ops q) =
      preparedHistoryContinue a s Ω ops (restrictedOriginalResponseReceive a s Ω q) := by
  induction q using Quotient.inductionOn with
  | _ h => rfl

end
end AASCKleinGordon
