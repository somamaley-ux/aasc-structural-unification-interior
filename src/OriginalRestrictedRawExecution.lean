import OriginalRestrictedRawSource

/-! A direct raw program source. Events retain actual raw origins and attempted
questions, including rejected operands. Answers and source comparisons are not
fields. Pure frame changes are the existing lawful presentation operations. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

structure RestrictedRawState where
  source : RestrictedRaw a Ω
  current : RestrictedRaw a Ω
  events : List (RestrictedRawEvent a Ω)

def restrictedRawInitial (x : RestrictedRaw a Ω) : RestrictedRawState a Ω := ⟨x, x, []⟩

def restrictedRawObserve (π : PreparedQuestion a Ω) (x : RestrictedRawState a Ω) :
    RestrictedRawState a Ω :=
  {x with events := x.events ++ [⟨x.current, π⟩]}

def restrictedRawVary (K : MetricSourceProbe Ω) (x : RestrictedRawState a Ω) :
    RestrictedRawState a Ω :=
  let H := x.current.act.val + K
  let recorded := restrictedRawObserve a Ω (preparedFiniteRequest a Ω H) x
  if inside : H ∈ wickOriginalMetricNeighborhood Ω then
    {recorded with current := restrictedRawReplace a Ω x.current H inside}
  else recorded

def restrictedRawStep (op : PreparedHistoryOperation a Ω) (x : RestrictedRawState a Ω) :
    RestrictedRawState a Ω :=
  match op with
  | .observe π => restrictedRawObserve a Ω π x
  | .vary K => restrictedRawVary a Ω K x
  | .frame _ => x

def restrictedRawRun : List (PreparedHistoryOperation a Ω) →
    RestrictedRawState a Ω → RestrictedRawState a Ω
  | [], x => x
  | op :: rest, x => restrictedRawRun rest (restrictedRawStep a Ω op x)

theorem restricted_raw_step_source (op : PreparedHistoryOperation a Ω) (x : RestrictedRawState a Ω) :
    (restrictedRawStep a Ω op x).source = x.source := by
  cases op with
  | observe _ => rfl
  | frame _ => rfl
  | vary _ => unfold restrictedRawStep restrictedRawVary; dsimp only; split <;> rfl

theorem restricted_raw_step_current (op : PreparedHistoryOperation a Ω) (x : RestrictedRawState a Ω) :
    restrictedRawReceive a s Ω (restrictedRawStep a Ω op x).current =
      preparedOriginalOperation a s Ω op (restrictedRawReceive a s Ω x.current) := by
  cases op with
  | observe _ => rfl
  | frame _ => rfl
  | vary K =>
    change restrictedRawReceive a s Ω (restrictedRawVary a Ω K x).current =
      if inside : x.current.act.val + K ∈ wickOriginalMetricNeighborhood Ω then
        preparedReplaceAct a s Ω (restrictedRawReceive a s Ω x.current)
          (x.current.act.val + K) inside
      else restrictedRawReceive a s Ω x.current
    by_cases inside : x.current.act.val + K ∈ wickOriginalMetricNeighborhood Ω
    · simp only [restrictedRawVary, dif_pos inside]
      exact restricted_raw_replace_square a s Ω x.current _ inside
    · simp only [restrictedRawVary, dif_neg inside]
      rfl

theorem restricted_raw_step_emission (op : PreparedHistoryOperation a Ω) (x : RestrictedRawState a Ω) :
    ((restrictedRawStep a Ω op x).events.map (restrictedRawEventReceive a s Ω)) =
      x.events.map (restrictedRawEventReceive a s Ω) ++
        (preparedOriginalOperationEvent a s Ω op (restrictedRawReceive a s Ω x.current)).toList := by
  cases op with
  | observe π =>
    simp [restrictedRawStep, restrictedRawObserve, preparedOriginalOperationEvent,
      restrictedRawEventReceive]
  | frame _ => simp [restrictedRawStep, preparedOriginalOperationEvent]
  | vary K =>
    unfold restrictedRawStep restrictedRawVary
    dsimp only
    split <;> simp [restrictedRawObserve, preparedOriginalOperationEvent, restrictedRawEventReceive] <;> rfl

def RestrictedRawMatches (x : RestrictedRawState a Ω) (y : PreparedHistoryState a s Ω) : Prop :=
  restrictedRawReceive a s Ω x.source = y.source ∧
    restrictedRawReceive a s Ω x.current = preparedOriginalBase a s Ω y.locus ∧
    x.events.map (restrictedRawEventReceive a s Ω) = y.events

theorem restricted_raw_step_matches (op : PreparedHistoryOperation a Ω)
    (x : RestrictedRawState a Ω) (y : PreparedHistoryState a s Ω)
    (same : RestrictedRawMatches a s Ω x y) :
    RestrictedRawMatches a s Ω (restrictedRawStep a Ω op x) (preparedHistoryStep a s Ω op y) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (congrArg (restrictedRawReceive a s Ω) (restricted_raw_step_source a Ω op x)).trans
      (same.1.trans (prepared_history_step_source a s Ω op y).symm)
  · exact (restricted_raw_step_current a s Ω op x).trans
      ((congrArg (preparedOriginalOperation a s Ω op) same.2.1).trans
        (prepared_original_operation_step_square a s Ω op y).symm)
  · rw [restricted_raw_step_emission, prepared_operation_event_is_actual_emission,
      same.2.2, same.2.1]

theorem restricted_raw_run_matches (ops : List (PreparedHistoryOperation a Ω))
    (x : RestrictedRawState a Ω) (y : PreparedHistoryState a s Ω)
    (same : RestrictedRawMatches a s Ω x y) :
    RestrictedRawMatches a s Ω (restrictedRawRun a Ω ops x) (preparedHistoryRun a s Ω ops y) := by
  induction ops generalizing x y with
  | nil => exact same
  | cons op rest ih => exact ih _ _ (restricted_raw_step_matches a s Ω op x y same)

structure RestrictedRawHistory where
  frame : ProperPoincareTransform
  initial : RestrictedRaw a Ω
  program : List (PreparedHistoryOperation a Ω)

def restrictedRawHistoryRun (h : RestrictedRawHistory a Ω) : RestrictedRawState a Ω :=
  restrictedRawRun a Ω h.program (restrictedRawInitial a Ω h.initial)

def restrictedRawHistoryPresent (h : RestrictedRawHistory a Ω) : PreparedOriginalHistory a s Ω :=
  ⟨preparedOriginalInFrame a s Ω h.frame (restrictedRawReceive a s Ω h.initial), h.program⟩

def restrictedRawHistoryAppend (h : RestrictedRawHistory a Ω)
    (ops : List (PreparedHistoryOperation a Ω)) : RestrictedRawHistory a Ω :=
  {h with program := h.program ++ ops}

theorem restricted_raw_history_run_matches (h : RestrictedRawHistory a Ω) :
    RestrictedRawMatches a s Ω (restrictedRawHistoryRun a Ω h)
      (preparedOriginalHistoryRun a s Ω (restrictedRawHistoryPresent a s Ω h)) := by
  apply restricted_raw_run_matches
  have base := prepared_original_base_in_frame a s Ω h.frame (restrictedRawReceive a s Ω h.initial)
  exact ⟨base.symm, base.symm, rfl⟩

theorem restricted_raw_history_append_present (h : RestrictedRawHistory a Ω)
    (ops : List (PreparedHistoryOperation a Ω)) :
    restrictedRawHistoryPresent a s Ω (restrictedRawHistoryAppend a Ω h ops) =
      preparedOriginalHistoryAppend a s Ω (restrictedRawHistoryPresent a s Ω h) ops := rfl

/-- Objectwise lifting of the independently existing prepared-history source.
No uniform raw representative selector and no supplied agreement field. -/
theorem restricted_raw_history_covers_prepared_histories :
    Function.Surjective (restrictedRawHistoryPresent a s Ω) := by
  intro h
  cases h with
  | mk initial program =>
    obtain ⟨x, hx⟩ := Quotient.exists_rep (preparedOriginalBase a s Ω initial)
    refine ⟨⟨initial.1, x, program⟩, ?_⟩
    change PreparedOriginalHistory.mk
      (preparedOriginalInFrame a s Ω initial.1 (restrictedRawReceive a s Ω x)) program = _
    change restrictedRawReceive a s Ω x = preparedOriginalBase a s Ω initial at hx
    rw [hx, prepared_original_in_frame_base]

end
end AASCKleinGordon
