import SKGSourceLocality

/-! Source readers for actual globally regular extensions of the local
scalar histories. Initial data, restrictions and constructed continuations
have this regularity. No global regularity is inferred for every local state. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource
attribute [local instance] Classical.propDecidable

structure RegularScalarSourceState (a : Parameters) where
  localState : CurvedScalarUseState a
  globalRegular : ContDiff ℝ (⊤ : ℕ∞) localState.field

def initialScalarSourceState (a : Parameters) (f h : CurvedCauchyDatum a) : RegularScalarSourceState a :=
  ⟨initialCurvedScalarUseState a f h, source_field_smooth a f h⟩

def restrictScalarSourceState (a : Parameters) (state : RegularScalarSourceState a)
    (W : Opens CoordinatePoint) (inside : W ≤ state.localState.domain) : RegularScalarSourceState a :=
  ⟨restrictCurvedScalarUseState a state.localState W inside, state.globalRegular⟩

def continuedScalarSourceState (a : Parameters) (state : RegularScalarSourceState a)
    (request : ScalarContinuationRequest) (inside : scalarContinuationDomain a request ≤ state.localState.domain) :
    RegularScalarSourceState a :=
  ⟨continuedCurvedScalarState a state.localState request inside,
    shifted_curved_smooth a request.time request.position request.velocity⟩

inductive ScalarSourceReaderKind where
  | linear | tensorPair | actionDerivative

inductive ScalarSourceQuestion (a : Parameters) where
  | stress (p : CoordinatePoint) (i j : Fin 4)
  | density (p : CoordinatePoint) (i : Fin 10)
  | response (kind : ScalarSourceReaderKind) (h : MetricSourceProbe (sourceDomain a))

def sourceQuestionAllowed (a : Parameters) (state : RegularScalarSourceState a) : ScalarSourceQuestion a → Prop
  | .stress p _ _ => p ∈ state.localState.domain
  | .density p _ => p ∈ state.localState.domain
  | .response _ h => tsupport h ⊆ state.localState.domain

def scalarSourceRawValue (a : Parameters) (state : RegularScalarSourceState a) : ScalarSourceQuestion a → ℝ
  | .stress p i j => sameSourceStress a state.localState.field p i j
  | .density p i => actualSourceDensityCoordinates a state.localState.field i p
  | .response .linear h => sameActionScalarMetricLF a state.localState.field
      (scalarSmoothTwo _ state.globalRegular) h
  | .response .tensorPair h => (1 / 2 : ℝ) * metricSourcePairing
      (sameActionScalarSource a state.localState.field (scalarSmoothTwo _ state.globalRegular)) h
  | .response .actionDerivative h => scalarMetricRayOutput a state.localState.field ⟨h⟩

theorem scalar_source_reader_square (a : Parameters) (state : RegularScalarSourceState a)
    (kind : ScalarSourceReaderKind) (h : MetricSourceProbe (sourceDomain a)) :
    scalarSourceRawValue a state (.response kind h) =
      sameActionScalarMetricLF a state.localState.field (scalarSmoothTwo _ state.globalRegular) h := by
  cases kind with
  | linear => rfl
  | tensorPair => exact constructed_metric_source_represents _ _
  | actionDerivative => exact same_action_ray_output_is_constructed_response a _ _ _

inductive ScalarSourceUseFailure where
  | incompatibleMetric | outsideDomain
  deriving DecidableEq

def scalarSourceRead (a : Parameters) (metric : MetricField) (state : RegularScalarSourceState a)
    (question : ScalarSourceQuestion a) : Except ScalarSourceUseFailure ℝ :=
  if metric = sourceMetric a then
    if sourceQuestionAllowed a state question then .ok (scalarSourceRawValue a state question)
    else .error .outsideDomain
  else .error .incompatibleMetric

def scalarSourceReadList (a : Parameters) (metric : MetricField) (state : RegularScalarSourceState a)
    (questions : List (ScalarSourceQuestion a)) : List (Except ScalarSourceUseFailure ℝ) :=
  questions.map (scalarSourceRead a metric state)

def firstScalarSourceFailure (events : List (Except ScalarSourceUseFailure ℝ)) : Option ScalarSourceUseFailure :=
  events.findSome? (fun event => match event with | .ok _ => none | .error failure => some failure)

theorem scalar_source_outside_failed (a : Parameters) (state : RegularScalarSourceState a)
    (question : ScalarSourceQuestion a) (outside : ¬sourceQuestionAllowed a state question) :
    scalarSourceRead a (sourceMetric a) state question = .error .outsideDomain := by
  simp [scalarSourceRead, outside]

theorem scalar_source_metric_change_failed (a : Parameters) (metric : MetricField)
    (state : RegularScalarSourceState a) (question : ScalarSourceQuestion a)
    (incompatible : metric ≠ sourceMetric a) :
    scalarSourceRead a metric state question = .error .incompatibleMetric := by
  simp [scalarSourceRead, incompatible]

theorem scalar_source_raw_value_local (a : Parameters) (state other : RegularScalarSourceState a)
    (same : ScalarUseSame a state.localState other.localState) (question : ScalarSourceQuestion a)
    (allowed : sourceQuestionAllowed a state question) :
    scalarSourceRawValue a state question = scalarSourceRawValue a other question := by
  cases question with
  | stress p i j =>
    exact congrArg (fun M : Tensor2 => M i j)
      (scalar_stress_local a _ _ state.localState.domain same.2 p allowed)
  | density p i => exact scalar_density_local a _ _ state.localState.domain same.2 p allowed i
  | response kind h =>
    rw [scalar_source_reader_square, scalar_source_reader_square]
    exact scalar_response_local a _ _ _ _ state.localState.domain same.2 h allowed

theorem scalar_source_read_local (a : Parameters) (metric : MetricField)
    (state other : RegularScalarSourceState a) (same : ScalarUseSame a state.localState other.localState)
    (question : ScalarSourceQuestion a) :
    scalarSourceRead a metric state question = scalarSourceRead a metric other question := by
  have scope : sourceQuestionAllowed a state question ↔ sourceQuestionAllowed a other question := by
    cases question <;> simp only [sourceQuestionAllowed, same.1]
  unfold scalarSourceRead
  by_cases compatible : metric = sourceMetric a
  · simp only [compatible, if_true]
    by_cases allowed : sourceQuestionAllowed a state question
    · rw [if_pos allowed, if_pos (scope.mp allowed), scalar_source_raw_value_local a state other same question allowed]
    · rw [if_neg allowed, if_neg (fun h => allowed (scope.mpr h))]
  · simp only [compatible, if_false]

theorem scalar_source_records_and_failures_local (a : Parameters) (metric : MetricField)
    (state other : RegularScalarSourceState a) (same : ScalarUseSame a state.localState other.localState)
    (questions : List (ScalarSourceQuestion a)) :
    scalarSourceReadList a metric state questions = scalarSourceReadList a metric other questions ∧
      firstScalarSourceFailure (scalarSourceReadList a metric state questions) =
        firstScalarSourceFailure (scalarSourceReadList a metric other questions) := by
  have records : scalarSourceReadList a metric state questions = scalarSourceReadList a metric other questions := by
    unfold scalarSourceReadList
    apply List.map_congr_left
    intro question _
    exact scalar_source_read_local a metric state other same question
  exact ⟨records, congrArg firstScalarSourceFailure records⟩

theorem scalar_source_continuation_compatibility (a : Parameters) (metric : MetricField)
    (state : RegularScalarSourceState a) (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.localState.domain)
    (matching : scalarContinuationDataMatch a state.localState request) (questions : List (ScalarSourceQuestion a)) :
    scalarSourceReadList a metric (continuedScalarSourceState a state request inside) questions =
      scalarSourceReadList a metric (restrictScalarSourceState a state (scalarContinuationDomain a request) inside) questions ∧
    firstScalarSourceFailure (scalarSourceReadList a metric (continuedScalarSourceState a state request inside) questions) =
      firstScalarSourceFailure (scalarSourceReadList a metric (restrictScalarSourceState a state (scalarContinuationDomain a request) inside) questions) :=
  scalar_source_records_and_failures_local a metric _ _
    (continued_state_is_restriction a state.localState request nonzero inside matching) questions

theorem scalar_source_restriction_compatibility (a : Parameters) (metric : MetricField)
    (state : RegularScalarSourceState a) (W : Opens CoordinatePoint) (inside : W ≤ state.localState.domain)
    (question : ScalarSourceQuestion a)
    (allowed : sourceQuestionAllowed a (restrictScalarSourceState a state W inside) question) :
    scalarSourceRead a metric (restrictScalarSourceState a state W inside) question =
      scalarSourceRead a metric state question := by
  have allowedOriginal : sourceQuestionAllowed a state question := by
    cases question with
    | stress p i j => exact inside allowed
    | density p i => exact inside allowed
    | response kind h => exact allowed.trans inside
  have raw : scalarSourceRawValue a (restrictScalarSourceState a state W inside) question =
      scalarSourceRawValue a state question := by
    cases question with
    | stress p i j => rfl
    | density p i => rfl
    | response kind h => cases kind <;> rfl
  unfold scalarSourceRead
  by_cases compatible : metric = sourceMetric a
  · simp only [compatible, if_true, allowed, allowedOriginal, raw]
  · simp only [compatible, if_false]

end AASCKleinGordon.SameActionSource
