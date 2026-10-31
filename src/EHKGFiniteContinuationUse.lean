import EHKGContinuationLaws

/-! Finite observation/restriction/continuation programs with complete
failure events. Invalid continuation keeps its pre-operation state and
records the exact rejected condition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

inductive CurvedKGOperation where
  | basic (operation : ScalarUseOperation)
  | continueFrom (request : ScalarContinuationRequest)

structure CurvedKGUseEvent where
  answer : Option ℝ
  failure : Option (Sum CurvedScalarUseFailure ScalarContinuationFailure)

def curvedKGStep (a : Parameters) (state : CurvedScalarUseState a) :
    CurvedKGOperation → CurvedScalarUseState a × CurvedKGUseEvent
  | .basic op =>
    let result := scalarUseStep a state op
    (result.1, ⟨result.2.answer, result.2.failure.map Sum.inl⟩)
  | .continueFrom request => match scalarContinue a state request with
    | .error failure => (state, ⟨none, some (.inr failure)⟩)
    | .ok next => (next, ⟨none, none⟩)

def curvedKGRun (a : Parameters) (state : CurvedScalarUseState a) :
    List CurvedKGOperation → CurvedScalarUseState a × List CurvedKGUseEvent
  | [] => (state, [])
  | op :: rest =>
    let step := curvedKGStep a state op
    let tail := curvedKGRun a step.1 rest
    (tail.1, step.2 :: tail.2)

def firstCurvedKGFailure : List CurvedKGUseEvent →
    Option (ℕ × Sum CurvedScalarUseFailure ScalarContinuationFailure)
  | [] => none
  | ev :: rest => match ev.failure with
    | some failure => some (0, failure)
    | none => (firstCurvedKGFailure rest).map (fun pair => (pair.1 + 1, pair.2))

theorem curved_kg_step_same (a : Parameters) (state other : CurvedScalarUseState a)
    (same : ScalarUseSame a state other) (op : CurvedKGOperation) :
    ScalarUseSame a (curvedKGStep a state op).1 (curvedKGStep a other op).1 ∧
      (curvedKGStep a state op).2 = (curvedKGStep a other op).2 := by
  cases op with
  | basic op =>
    have step := scalar_use_step_same a state other same op
    refine ⟨step.1, ?_⟩
    exact congrArg (fun ev : ScalarUseEvent => (⟨ev.answer, ev.failure.map Sum.inl⟩ : CurvedKGUseEvent)) step.2
  | continueFrom request =>
    have step := scalar_continue_same a state other same request
    cases first : scalarContinue a state request with
    | error failure =>
      cases second : scalarContinue a other request with
      | error otherFailure =>
        simp only [first, second, ScalarContinuationOutcomeSame] at step
        simp only [curvedKGStep, first, second]
        exact ⟨same, congrArg (fun f => (⟨none, some (.inr f)⟩ : CurvedKGUseEvent)) step⟩
      | ok next =>
        simp only [first, second, ScalarContinuationOutcomeSame] at step
    | ok next =>
      cases second : scalarContinue a other request with
      | error failure =>
        simp only [first, second, ScalarContinuationOutcomeSame] at step
      | ok otherNext =>
        simp only [first, second, ScalarContinuationOutcomeSame] at step
        simp only [curvedKGStep, first, second]
        exact ⟨step, trivial⟩

theorem curved_kg_run_same (a : Parameters) (program : List CurvedKGOperation)
    (state other : CurvedScalarUseState a) (same : ScalarUseSame a state other) :
    ScalarUseSame a (curvedKGRun a state program).1 (curvedKGRun a other program).1 ∧
      (curvedKGRun a state program).2 = (curvedKGRun a other program).2 := by
  induction program generalizing state other with
  | nil => exact ⟨same, rfl⟩
  | cons op rest ih =>
    have step := curved_kg_step_same a state other same op
    have tail := ih _ _ step.1
    exact ⟨tail.1, congrArg₂ List.cons step.2 tail.2⟩

theorem curved_kg_first_failure_same (a : Parameters) (program : List CurvedKGOperation)
    (state other : CurvedScalarUseState a) (same : ScalarUseSame a state other) :
    firstCurvedKGFailure (curvedKGRun a state program).2 =
      firstCurvedKGFailure (curvedKGRun a other program).2 :=
  congrArg firstCurvedKGFailure (curved_kg_run_same a program state other same).2

theorem curved_kg_run_append (a : Parameters) (state : CurvedScalarUseState a)
    (first second : List CurvedKGOperation) :
    curvedKGRun a state (first ++ second) =
      ((curvedKGRun a (curvedKGRun a state first).1 second).1,
        (curvedKGRun a state first).2 ++
          (curvedKGRun a (curvedKGRun a state first).1 second).2) := by
  induction first generalizing state with
  | nil => rfl
  | cons op rest ih =>
    change ((curvedKGRun a (curvedKGStep a state op).1 (rest ++ second)).1,
      (curvedKGStep a state op).2 :: (curvedKGRun a (curvedKGStep a state op).1 (rest ++ second)).2) = _
    rw [ih]
    rfl

theorem curved_kg_failed_continuation_retained (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (failure : ScalarContinuationFailure)
    (rejected : scalarContinue a state request = .error failure) :
    curvedKGStep a state (.continueFrom request) = (state, ⟨none, some (.inr failure)⟩) := by
  simp only [curvedKGStep, rejected]

theorem continuation_retains_all_curved_programs (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) (matching : scalarContinuationDataMatch a state request)
    (program : List CurvedKGOperation) :
    (curvedKGRun a (continuedCurvedScalarState a state request inside) program).2 =
        (curvedKGRun a (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) program).2 ∧
    firstCurvedKGFailure (curvedKGRun a (continuedCurvedScalarState a state request inside) program).2 =
        firstCurvedKGFailure (curvedKGRun a (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) program).2 := by
  have same := continued_state_is_restriction a state request nonzero inside matching
  exact ⟨(curved_kg_run_same a program _ _ same).2, curved_kg_first_failure_same a program _ _ same⟩

end AASCKleinGordon.CurvedKG
