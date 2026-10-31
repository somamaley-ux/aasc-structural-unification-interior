import EHKGScalarUseState

/-! Finite actual scalar observation/restriction programs, with explicit
failure events and retained first failures. Local field equality preserves
all finite contexts, including invalid restrictions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG
attribute [local instance] Classical.propDecidable

inductive ScalarUseOperation where
  | observe (question : CurvedScalarQuestion)
  | restrictTo (domain : Opens CoordinatePoint)

structure ScalarUseEvent where
  answer : Option ℝ
  failure : Option CurvedScalarUseFailure

noncomputable def scalarUseStep (a : Parameters) (state : CurvedScalarUseState a) :
    ScalarUseOperation → CurvedScalarUseState a × ScalarUseEvent
  | .observe q => (state, ⟨scalarQuestionAnswer a state q, scalarQuestionFailure a state q⟩)
  | .restrictTo W => if inside : W ≤ state.domain then
      (restrictCurvedScalarUseState a state W inside, ⟨none, none⟩)
    else (state, ⟨none, some .invalidRestriction⟩)

def scalarUseRun (a : Parameters) (state : CurvedScalarUseState a) :
    List ScalarUseOperation → CurvedScalarUseState a × List ScalarUseEvent
  | [] => (state, [])
  | op :: rest =>
    let step := scalarUseStep a state op
    let tail := scalarUseRun a step.1 rest
    (tail.1, step.2 :: tail.2)

def firstScalarUseFailure : List ScalarUseEvent → Option (ℕ × CurvedScalarUseFailure)
  | [] => none
  | ev :: rest => match ev.failure with
    | some failure => some (0, failure)
    | none => (firstScalarUseFailure rest).map (fun pair => (pair.1 + 1, pair.2))

theorem scalar_use_step_same (a : Parameters) (state other : CurvedScalarUseState a)
    (same : ScalarUseSame a state other) (op : ScalarUseOperation) :
    ScalarUseSame a (scalarUseStep a state op).1 (scalarUseStep a other op).1 ∧
      (scalarUseStep a state op).2 = (scalarUseStep a other op).2 := by
  cases op with
  | observe q =>
    refine ⟨same, ?_⟩
    exact congrArg₂ ScalarUseEvent.mk
      (scalar_use_same_preserves_answers a state other same q)
      (scalar_use_same_preserves_failures a state other same q)
  | restrictTo W =>
    by_cases inside : W ≤ state.domain
    · have insideOther : W ≤ other.domain := by rw [← same.1]; exact inside
      simp only [scalarUseStep, dif_pos inside, dif_pos insideOther]
      exact ⟨⟨rfl, fun p hp => same.2 (inside hp)⟩, trivial⟩
    · have outsideOther : ¬ W ≤ other.domain := by rw [← same.1]; exact inside
      simp only [scalarUseStep, dif_neg inside, dif_neg outsideOther]
      exact ⟨same, trivial⟩

theorem scalar_use_run_same (a : Parameters) (program : List ScalarUseOperation)
    (state other : CurvedScalarUseState a) (same : ScalarUseSame a state other) :
    ScalarUseSame a (scalarUseRun a state program).1 (scalarUseRun a other program).1 ∧
      (scalarUseRun a state program).2 = (scalarUseRun a other program).2 := by
  induction program generalizing state other with
  | nil => exact ⟨same, rfl⟩
  | cons op rest ih =>
    have step := scalar_use_step_same a state other same op
    have tail := ih _ _ step.1
    exact ⟨tail.1, congrArg₂ List.cons step.2 tail.2⟩

theorem scalar_use_first_failure_same (a : Parameters) (program : List ScalarUseOperation)
    (state other : CurvedScalarUseState a) (same : ScalarUseSame a state other) :
    firstScalarUseFailure (scalarUseRun a state program).2 =
      firstScalarUseFailure (scalarUseRun a other program).2 :=
  congrArg firstScalarUseFailure (scalar_use_run_same a program state other same).2

theorem scalar_use_run_append (a : Parameters) (state : CurvedScalarUseState a)
    (first second : List ScalarUseOperation) :
    scalarUseRun a state (first ++ second) =
      ((scalarUseRun a (scalarUseRun a state first).1 second).1,
        (scalarUseRun a state first).2 ++
          (scalarUseRun a (scalarUseRun a state first).1 second).2) := by
  induction first generalizing state with
  | nil => rfl
  | cons op rest ih =>
    change ((scalarUseRun a (scalarUseStep a state op).1 (rest ++ second)).1,
      (scalarUseStep a state op).2 :: (scalarUseRun a (scalarUseStep a state op).1 (rest ++ second)).2) = _
    rw [ih]
    rfl

theorem scalar_use_event_count (a : Parameters) (state : CurvedScalarUseState a)
    (program : List ScalarUseOperation) : (scalarUseRun a state program).2.length = program.length := by
  induction program generalizing state with
  | nil => rfl
  | cons op rest ih => exact congrArg Nat.succ (ih (scalarUseStep a state op).1)

theorem scalar_invalid_restriction_retained (a : Parameters) (state : CurvedScalarUseState a)
    (W : Opens CoordinatePoint) (invalid : ¬ W ≤ state.domain) :
    scalarUseStep a state (.restrictTo W) = (state, ⟨none, some .invalidRestriction⟩) := by
  simp only [scalarUseStep, dif_neg invalid]

end AASCKleinGordon.CurvedKG
