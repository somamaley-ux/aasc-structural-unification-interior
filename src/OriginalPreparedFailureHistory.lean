import OriginalPreparedProtocolStep

/-! Computed histories of the existing prepared-protocol branch. A failed
registered observation remains a typed event; it does not stop subsequent
operations. Updating the prepared metric operand is distinguished from an
Einstein evolution or an unspecified physical effect of a failed act. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

structure PreparedHistoryState where
  source : PreparedOriginal a s Ω
  locus : PreparedLocus a s Ω
  events : List (PreparedEvent a s Ω)

def preparedHistoryInitial (x : PreparedLocus a s Ω) : PreparedHistoryState a s Ω :=
  ⟨preparedOriginalBase a s Ω x,x,[]⟩

def preparedHistoryObserve (π : PreparedQuestion a Ω) (x : PreparedHistoryState a s Ω) :
    PreparedHistoryState a s Ω :=
  {x with events := x.events ++ [⟨preparedOriginalBase a s Ω x.locus,π⟩]}

/-- The attempted operand is retained by its original finite-request question.
Only admission in the OLD domain changes the selected prepared operand. -/
def preparedHistoryVary (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω) :
    PreparedHistoryState a s Ω := by
  classical
  let z := preparedOriginalBase a s Ω x.locus
  let H := (originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K
  let recorded := preparedHistoryObserve a s Ω (preparedFiniteRequest a Ω H) x
  exact if inside : H ∈ wickOriginalMetricNeighborhood Ω then
    {recorded with locus := (preparedOriginalInFrame a s Ω x.locus.1
      (preparedReplaceAct a s Ω z H inside))} else recorded

def preparedHistoryFrame (q : ProperPoincareTransform) (x : PreparedHistoryState a s Ω) :
    PreparedHistoryState a s Ω :=
  {x with locus := kgJointFrameLocusChange s Ω (kgOriginalObject a) q x.locus}

inductive PreparedHistoryOperation where
  | observe (question : PreparedQuestion a Ω)
  | vary (test : MetricSourceProbe Ω)
  | frame (target : ProperPoincareTransform)

def preparedHistoryStep (operation : PreparedHistoryOperation a Ω)
    (x : PreparedHistoryState a s Ω) : PreparedHistoryState a s Ω :=
  match operation with
  | .observe π => preparedHistoryObserve a s Ω π x
  | .vary K => preparedHistoryVary a s Ω K x
  | .frame q => preparedHistoryFrame a s Ω q x

def preparedHistoryRun : List (PreparedHistoryOperation a Ω) →
    PreparedHistoryState a s Ω → PreparedHistoryState a s Ω
  | [],x => x
  | operation::rest,x => preparedHistoryRun rest (preparedHistoryStep a s Ω operation x)

theorem prepared_history_run_append (first second : List (PreparedHistoryOperation a Ω))
    (x : PreparedHistoryState a s Ω) :
    preparedHistoryRun a s Ω (first++second) x =
      preparedHistoryRun a s Ω second (preparedHistoryRun a s Ω first x) := by
  induction first generalizing x with
  | nil => rfl
  | cons operation rest ih => exact ih _

theorem prepared_history_step_source (operation : PreparedHistoryOperation a Ω)
    (x : PreparedHistoryState a s Ω) :
    (preparedHistoryStep a s Ω operation x).source = x.source := by
  classical
  cases operation with
  | observe π => rfl
  | frame q => rfl
  | vary K =>
    unfold preparedHistoryStep preparedHistoryVary
    dsimp only
    split <;> rfl

theorem prepared_history_run_source (operations : List (PreparedHistoryOperation a Ω))
    (x : PreparedHistoryState a s Ω) :
    (preparedHistoryRun a s Ω operations x).source = x.source := by
  induction operations generalizing x with
  | nil => rfl
  | cons operation rest ih => exact (ih _).trans (prepared_history_step_source a s Ω operation x)

theorem prepared_history_vary_events (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω) :
    (preparedHistoryVary a s Ω K x).events = x.events ++
      [⟨preparedOriginalBase a s Ω x.locus,preparedFiniteRequest a Ω
        ((originalEHPreparedAct s Ω (kgOriginalObject a)
          (preparedOriginalBase a s Ω x.locus)).val+K)⟩] := by
  classical
  unfold preparedHistoryVary
  dsimp only
  split <;> rfl

theorem prepared_history_step_events_prefix (operation : PreparedHistoryOperation a Ω)
    (x : PreparedHistoryState a s Ω) :
    ∃ tail,(preparedHistoryStep a s Ω operation x).events = x.events ++ tail := by
  cases operation with
  | observe π => exact ⟨_,rfl⟩
  | vary K => exact ⟨_,prepared_history_vary_events a s Ω K x⟩
  | frame q => exact ⟨[],(List.append_nil _).symm⟩

theorem prepared_history_run_events_prefix (operations : List (PreparedHistoryOperation a Ω))
    (x : PreparedHistoryState a s Ω) :
    ∃ tail,(preparedHistoryRun a s Ω operations x).events = x.events ++ tail := by
  induction operations generalizing x with
  | nil => exact ⟨[],(List.append_nil _).symm⟩
  | cons operation rest ih =>
    obtain ⟨left,hleft⟩ := prepared_history_step_events_prefix a s Ω operation x
    obtain ⟨right,hright⟩ := ih (preparedHistoryStep a s Ω operation x)
    exact ⟨left++right,hright.trans (by rw [hleft,List.append_assoc])⟩

def preparedHistoryFirstFailure : List (PreparedEvent a s Ω) → Option (ℕ × KGExecutionFailure)
  | [] => none
  | e::rest => match preparedEventFailure a s Ω e with
    | some reason => some (0,reason)
    | none => (preparedHistoryFirstFailure rest).map (fun p => (p.1+1,p.2))

theorem prepared_history_first_failure_append (first second : List (PreparedEvent a s Ω)) :
    preparedHistoryFirstFailure a s Ω (first++second) =
      match preparedHistoryFirstFailure a s Ω first with
      | some failure => some failure
      | none => (preparedHistoryFirstFailure a s Ω second).map
          (fun p => (p.1+first.length,p.2)) := by
  induction first with
  | nil => simp [preparedHistoryFirstFailure]
  | cons e rest ih =>
    cases he : preparedEventFailure a s Ω e with
    | some reason => simp [preparedHistoryFirstFailure,he]
    | none =>
      simp only [List.cons_append,preparedHistoryFirstFailure,he,ih]
      cases hr : preparedHistoryFirstFailure a s Ω rest with
      | some failure => rfl
      | none =>
        cases hs : preparedHistoryFirstFailure a s Ω second with
        | none => rfl
        | some failure => simp [Option.map,Nat.add_assoc]

theorem prepared_history_first_failure_retained
    (operations : List (PreparedHistoryOperation a Ω)) (x : PreparedHistoryState a s Ω)
    (n : ℕ) (reason : KGExecutionFailure)
    (failed : preparedHistoryFirstFailure a s Ω x.events = some (n,reason)) :
    preparedHistoryFirstFailure a s Ω (preparedHistoryRun a s Ω operations x).events =
      some (n,reason) := by
  obtain ⟨tail,htail⟩ := prepared_history_run_events_prefix a s Ω operations x
  rw [htail,prepared_history_first_failure_append,failed]

theorem prepared_history_ledger_report_not_execution_failure (z : PreparedOriginal a s Ω)
    (π : KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    preparedEventFailure a s Ω ⟨z,.inr (.ledger π)⟩ = none := rfl

theorem prepared_history_observation_does_not_stop (π : PreparedQuestion a Ω)
    (x : PreparedHistoryState a s Ω) (rest : List (PreparedHistoryOperation a Ω)) :
    preparedHistoryRun a s Ω (.observe π::rest) x =
      preparedHistoryRun a s Ω rest (preparedHistoryObserve a s Ω π x) := rfl

end
end AASCKleinGordon
