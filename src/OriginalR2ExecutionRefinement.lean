import OriginalR2LocalUseConsequences
import OriginalPreparedHistoryContexts

/-! Actual joint execution refinement for the declared original prepared-use
role. The source is initial-use/program records; answers and failures are run,
not supplied. Lineage comparisons below use actual append incidences. Neither
equality of quantum rays nor an unused source tag asserts physical event identity.
The receiver is the already constructed contextual-history quotient. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def preparedExecutionTerminal (h : PreparedOriginalHistory a s Ω) : PreparedOriginal a s Ω :=
  preparedOriginalBase a s Ω (preparedOriginalHistoryRun a s Ω h).locus

def preparedExecutionFailure (h : PreparedOriginalHistory a s Ω) : Option (ℕ × KGExecutionFailure) :=
  preparedHistoryFirstFailure a s Ω (preparedOriginalHistoryRun a s Ω h).events

def preparedExecutionProjection (q : PreparedHistoryReceiver a s Ω) : PreparedOriginal a s Ω :=
  (preparedHistoryReadProfile a s Ω q).target

theorem prepared_execution_projection_square (h : PreparedOriginalHistory a s Ω) :
    preparedExecutionProjection a s Ω (preparedHistoryReceive a s Ω h) =
      preparedExecutionTerminal a s Ω h := rfl

theorem prepared_execution_projection_onto_old_carrier (frame : ProperPoincareTransform) :
    Function.Surjective (preparedExecutionProjection a s Ω) := by
  intro z
  refine ⟨preparedHistoryReceive a s Ω ⟨preparedOriginalInFrame a s Ω frame z, []⟩, ?_⟩
  exact prepared_original_base_in_frame a s Ω frame z

theorem prepared_execution_old_answer_retained (q : PreparedHistoryReceiver a s Ω)
    (π : PreparedQuestion a Ω) :
    preparedHistoryReference a s Ω q π =
      kgJointFrameOriginalAnswer s Ω (kgOriginalObject a)
        (preparedExecutionProjection a s Ω q) π := rfl

/-- Old terminal bookkeeping, including unchanged selected operand on rejection.
Rejection is still retained as a failed execution event by the richer receiver. -/
def preparedOriginalVariation (K : MetricSourceProbe Ω) (z : PreparedOriginal a s Ω) :
    PreparedOriginal a s Ω :=
  if inside : (originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K ∈
      wickOriginalMetricNeighborhood Ω then
    preparedReplaceAct a s Ω z
      ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K) inside
  else z

theorem prepared_execution_variation_projection_square (K : MetricSourceProbe Ω)
    (q : PreparedHistoryReceiver a s Ω) :
    preparedExecutionProjection a s Ω (preparedHistoryContinue a s Ω [.vary K] q) =
      preparedOriginalVariation a s Ω K (preparedExecutionProjection a s Ω q) := by
  induction q using Quotient.inductionOn with
  | _ h =>
    change preparedExecutionTerminal a s Ω
      (preparedOriginalHistoryAppend a s Ω h [.vary K]) = _
    unfold preparedExecutionTerminal
    rw [prepared_original_history_append_run]
    exact prepared_history_vary_base a s Ω K (preparedOriginalHistoryRun a s Ω h)

def preparedOriginalOperation (op : PreparedHistoryOperation a Ω)
    (z : PreparedOriginal a s Ω) : PreparedOriginal a s Ω :=
  match op with
  | .observe _ => z
  | .frame _ => z
  | .vary K => preparedOriginalVariation a s Ω K z

def preparedOriginalProgram : List (PreparedHistoryOperation a Ω) →
    PreparedOriginal a s Ω → PreparedOriginal a s Ω
  | [], z => z
  | op :: rest, z => preparedOriginalProgram rest (preparedOriginalOperation a s Ω op z)

theorem prepared_original_operation_step_square (op : PreparedHistoryOperation a Ω)
    (x : PreparedHistoryState a s Ω) :
    preparedOriginalBase a s Ω (preparedHistoryStep a s Ω op x).locus =
      preparedOriginalOperation a s Ω op (preparedOriginalBase a s Ω x.locus) := by
  cases op with
  | observe _ => rfl
  | frame frame => exact prepared_original_base_frame_change a s Ω frame x.locus
  | vary K => exact prepared_history_vary_base a s Ω K x

theorem prepared_original_program_run_square (ops : List (PreparedHistoryOperation a Ω))
    (x : PreparedHistoryState a s Ω) :
    preparedOriginalBase a s Ω (preparedHistoryRun a s Ω ops x).locus =
      preparedOriginalProgram a s Ω ops (preparedOriginalBase a s Ω x.locus) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op rest ih =>
    change preparedOriginalBase a s Ω
      (preparedHistoryRun a s Ω rest (preparedHistoryStep a s Ω op x)).locus = _
    rw [ih, prepared_original_operation_step_square]
    rfl

theorem prepared_execution_program_projection_square (ops : List (PreparedHistoryOperation a Ω))
    (q : PreparedHistoryReceiver a s Ω) :
    preparedExecutionProjection a s Ω (preparedHistoryContinue a s Ω ops q) =
      preparedOriginalProgram a s Ω ops (preparedExecutionProjection a s Ω q) := by
  induction q using Quotient.inductionOn with
  | _ h =>
    change preparedExecutionTerminal a s Ω (preparedOriginalHistoryAppend a s Ω h ops) = _
    unfold preparedExecutionTerminal
    rw [prepared_original_history_append_run]
    exact prepared_original_program_run_square a s Ω ops (preparedOriginalHistoryRun a s Ω h)

/-- Exact old diagnostic for this operation, distinct from terminal fallback. -/
def preparedOriginalOperationFailure (op : PreparedHistoryOperation a Ω)
    (z : PreparedOriginal a s Ω) : Option KGExecutionFailure :=
  match op with
  | .observe π => preparedEventFailure a s Ω ⟨z, π⟩
  | .frame _ => none
  | .vary K => preparedEventFailure a s Ω ⟨z, preparedFiniteRequest a Ω
      ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K)⟩

def preparedOriginalOperationEvent (op : PreparedHistoryOperation a Ω)
    (z : PreparedOriginal a s Ω) : Option (PreparedEvent a s Ω) :=
  match op with
  | .observe π => some ⟨z, π⟩
  | .frame _ => none
  | .vary K => some ⟨z, preparedFiniteRequest a Ω
      ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K)⟩

theorem prepared_operation_event_is_actual_emission (op : PreparedHistoryOperation a Ω)
    (x : PreparedHistoryState a s Ω) :
    (preparedHistoryStep a s Ω op x).events = x.events ++
      (preparedOriginalOperationEvent a s Ω op (preparedOriginalBase a s Ω x.locus)).toList := by
  cases op with
  | observe _ => rfl
  | frame _ => exact (List.append_nil x.events).symm
  | vary K => exact prepared_history_vary_events a s Ω K x

theorem prepared_operation_failure_is_actual_event_failure (op : PreparedHistoryOperation a Ω)
    (z : PreparedOriginal a s Ω) :
    preparedOriginalOperationFailure a s Ω op z =
      (preparedOriginalOperationEvent a s Ω op z).bind (preparedEventFailure a s Ω) := by
  cases op <;> rfl

def preparedOriginalPartialOperation (op : PreparedHistoryOperation a Ω)
    (z : PreparedOriginal a s Ω) : Option (PreparedOriginal a s Ω) :=
  if preparedOriginalOperationFailure a s Ω op z = none then
    some (preparedOriginalOperation a s Ω op z) else none

def preparedExecutionPartialOperation (op : PreparedHistoryOperation a Ω)
    (q : PreparedHistoryReceiver a s Ω) : Option (PreparedHistoryReceiver a s Ω) :=
  if preparedOriginalOperationFailure a s Ω op (preparedExecutionProjection a s Ω q) = none then
    some (preparedHistoryContinue a s Ω [op] q) else none

theorem prepared_execution_partial_operation_exact_receipt (op : PreparedHistoryOperation a Ω)
    (q : PreparedHistoryReceiver a s Ω) :
    (preparedExecutionPartialOperation a s Ω op q).map (preparedExecutionProjection a s Ω) =
      preparedOriginalPartialOperation a s Ω op (preparedExecutionProjection a s Ω q) := by
  unfold preparedExecutionPartialOperation preparedOriginalPartialOperation
  split
  · simp only [Option.map_some, prepared_execution_program_projection_square,
      preparedOriginalProgram]
  · rfl

theorem prepared_execution_source_is_actual_initial (h : PreparedOriginalHistory a s Ω) :
    (preparedOriginalHistoryRun a s Ω h).source = preparedOriginalBase a s Ω h.initial :=
  prepared_history_run_source a s Ω h.program (preparedHistoryInitial a s Ω h.initial)

def preparedExecutionEligibility (q : PreparedHistoryReceiver a s Ω)
    (L : MetricSourceProbe Ω) : Prop :=
  preparedProspectiveAdmission a s Ω (preparedExecutionProjection a s Ω q) L

def preparedExecutionBurden (q : PreparedHistoryReceiver a s Ω) : Set (MetricSourceProbe Ω) :=
  preparedCapabilityLoss a s Ω (preparedHistoryReadProfile a s Ω q).source
    (preparedExecutionProjection a s Ω q)

def preparedExecutionRepairDomain (target : PreparedOriginal a s Ω)
    (q : PreparedHistoryReceiver a s Ω) : Set (MetricSourceProbe Ω) :=
  {K | K ∈ preparedCorrectionBoundary a s Ω (preparedExecutionProjection a s Ω q) ∧
    preparedExecutionProjection a s Ω (preparedHistoryContinue a s Ω [.vary K] q) = target}

theorem prepared_execution_eligibility_square (h : PreparedOriginalHistory a s Ω)
    (L : MetricSourceProbe Ω) :
    preparedExecutionEligibility a s Ω (preparedHistoryReceive a s Ω h) L ↔
      preparedProspectiveAdmission a s Ω (preparedExecutionTerminal a s Ω h) L := Iff.rfl

theorem prepared_execution_burden_square (h : PreparedOriginalHistory a s Ω) :
    preparedExecutionBurden a s Ω (preparedHistoryReceive a s Ω h) =
      preparedCapabilityLoss a s Ω (preparedOriginalBase a s Ω h.initial)
        (preparedExecutionTerminal a s Ω h) := by
  change preparedCapabilityLoss a s Ω (preparedOriginalHistoryRun a s Ω h).source _ = _
  rw [prepared_execution_source_is_actual_initial]
  rfl

theorem prepared_execution_repair_domain_square (target : PreparedOriginal a s Ω)
    (h : PreparedOriginalHistory a s Ω) :
    preparedExecutionRepairDomain a s Ω target (preparedHistoryReceive a s Ω h) =
      preparedCorrectionDomain a s Ω target (preparedOriginalHistoryRun a s Ω h) := by
  ext K
  change (K ∈ preparedCorrectionBoundary a s Ω (preparedExecutionTerminal a s Ω h) ∧
    preparedExecutionTerminal a s Ω (preparedOriginalHistoryAppend a s Ω h [.vary K]) = target) ↔ _
  unfold preparedExecutionTerminal
  rw [prepared_original_history_append_run]
  rfl

theorem prepared_execution_disturbance_charges_original_burden
    (initial : PreparedLocus a s Ω) (K : MetricSourceProbe Ω) (nonzero : K ≠ 0)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω initial)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    (preparedExecutionBurden a s Ω
      (preparedHistoryReceive a s Ω ⟨initial, [.vary K]⟩)).Nonempty := by
  rw [prepared_execution_burden_square]
  exact prepared_nonzero_change_charges_lost_capability a s Ω K nonzero
    (preparedHistoryInitial a s Ω initial) inside

theorem prepared_execution_inverse_corrects_same_initial_use
    (initial : PreparedLocus a s Ω) (K : MetricSourceProbe Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω initial)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    -K ∈ preparedExecutionRepairDomain a s Ω (preparedOriginalBase a s Ω initial)
      (preparedHistoryReceive a s Ω ⟨initial, [.vary K]⟩) := by
  rw [prepared_execution_repair_domain_square]
  exact prepared_inverse_is_lawful_correction a s Ω K
    (preparedHistoryInitial a s Ω initial) inside

theorem prepared_execution_frame_preserves_role_responses
    (frame : ProperPoincareTransform) (h : PreparedOriginalHistory a s Ω)
    (target : PreparedOriginal a s Ω) :
    preparedExecutionBurden a s Ω
        (preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h [.frame frame])) =
      preparedExecutionBurden a s Ω (preparedHistoryReceive a s Ω h) ∧
    preparedExecutionRepairDomain a s Ω target
        (preparedHistoryReceive a s Ω (preparedOriginalHistoryAppend a s Ω h [.frame frame])) =
      preparedExecutionRepairDomain a s Ω target (preparedHistoryReceive a s Ω h) := by
  rw [prepared_history_frame_is_redescription]
  exact ⟨rfl, rfl⟩

/-- The same candidate lineage is witnessed by append, not inferred from ray equality. -/
theorem prepared_execution_append_keeps_original_initial (h : PreparedOriginalHistory a s Ω)
    (operations : List (PreparedHistoryOperation a Ω)) :
    (preparedOriginalHistoryAppend a s Ω h operations).initial = h.initial := rfl

theorem prepared_execution_failed_occurrence_persists
    (h : PreparedOriginalHistory a s Ω) (operations : List (PreparedHistoryOperation a Ω))
    (n : ℕ) (reason : KGExecutionFailure)
    (failed : preparedExecutionFailure a s Ω h = some (n, reason)) :
    preparedExecutionFailure a s Ω (preparedOriginalHistoryAppend a s Ω h operations) =
      some (n, reason) := by
  unfold preparedExecutionFailure
  rw [prepared_original_history_append_run]
  exact prepared_history_first_failure_retained a s Ω operations _ n reason failed

theorem prepared_execution_first_failure_none_iff (events : List (PreparedEvent a s Ω)) :
    preparedHistoryFirstFailure a s Ω events = none ↔
      ∀ e ∈ events, preparedEventFailure a s Ω e = none := by
  induction events with
  | nil => simp [preparedHistoryFirstFailure]
  | cons e rest ih =>
    cases hf : preparedEventFailure a s Ω e with
    | some reason => simp [preparedHistoryFirstFailure, hf]
    | none => simp [preparedHistoryFirstFailure, hf, ih]

def preparedRejectedCorrectedExecution (initial : PreparedLocus a s Ω)
    (K L : MetricSourceProbe Ω) : PreparedOriginalHistory a s Ω :=
  ⟨initial, [.vary K, .vary L, .vary (-K)]⟩

/-- A concrete collision: the same terminal prepared use cannot recover its
executed original failure. The empty and corrected executions share an actual
initial use; the second is its explicit original operation continuation. -/
theorem prepared_terminal_projection_loses_original_failure
    (initial : PreparedLocus a s Ω) (K : MetricSourceProbe Ω) (nonzero : K ≠ 0)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω initial)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ L : MetricSourceProbe Ω,
      preparedExecutionTerminal a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L) =
        preparedExecutionTerminal a s Ω ⟨initial, []⟩ ∧
      preparedExecutionFailure a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L) ≠ none ∧
      preparedExecutionFailure a s Ω ⟨initial, []⟩ = none := by
  let x := preparedHistoryInitial a s Ω initial
  obtain ⟨L, failure, present, _answer, restored, _future⟩ :=
    prepared_recorded_rejection_retained_after_operand_correction a s Ω K nonzero x inside
  refine ⟨L, restored, ?_, rfl⟩
  intro noFailure
  have allGood := (prepared_execution_first_failure_none_iff a s Ω _).mp noFailure
  have bad := allGood _ present
  rw [failure] at bad
  exact Option.some_ne_none _ bad

theorem prepared_original_failure_has_no_terminal_readout
    (initial : PreparedLocus a s Ω) (K : MetricSourceProbe Ω) (nonzero : K ≠ 0)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω initial)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ¬ ∃ f : PreparedOriginal a s Ω → Option (ℕ × KGExecutionFailure),
      ∀ h : PreparedOriginalHistory a s Ω,
        f (preparedExecutionTerminal a s Ω h) = preparedExecutionFailure a s Ω h := by
  obtain ⟨L, same, failed, empty⟩ :=
    prepared_terminal_projection_loses_original_failure a s Ω initial K nonzero inside
  rintro ⟨f, square⟩
  have eq := (square (preparedRejectedCorrectedExecution a s Ω initial K L)).symm.trans
    ((congrArg f same).trans (square ⟨initial, []⟩))
  exact failed (eq.trans empty)

theorem prepared_execution_refinement_retains_lost_failure
    (initial : PreparedLocus a s Ω) (K : MetricSourceProbe Ω) (nonzero : K ≠ 0)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω initial)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ L : MetricSourceProbe Ω,
      preparedExecutionProjection a s Ω
        (preparedHistoryReceive a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L)) =
      preparedExecutionProjection a s Ω (preparedHistoryReceive a s Ω ⟨initial, []⟩) ∧
      preparedHistoryReceive a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L) ≠
        preparedHistoryReceive a s Ω ⟨initial, []⟩ := by
  obtain ⟨L, same, failed, empty⟩ :=
    prepared_terminal_projection_loses_original_failure a s Ω initial K nonzero inside
  refine ⟨L, same, ?_⟩
  intro identified
  have failureEq := congrArg (preparedHistoryReadFirstFailure a s Ω) identified
  exact failed (failureEq.trans empty)

theorem prepared_restored_capability_does_not_clear_executed_failure
    (initial : PreparedLocus a s Ω) (K : MetricSourceProbe Ω) (nonzero : K ≠ 0)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω initial)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ L : MetricSourceProbe Ω,
      preparedExecutionBurden a s Ω
        (preparedHistoryReceive a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L)) = ∅ ∧
      preparedHistoryReadFirstFailure a s Ω
        (preparedHistoryReceive a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L)) ≠ none := by
  obtain ⟨L, same, failed, _empty⟩ :=
    prepared_terminal_projection_loses_original_failure a s Ω initial K nonzero inside
  refine ⟨L, ?_, failed⟩
  rw [prepared_execution_burden_square]
  change preparedCapabilityLoss a s Ω (preparedOriginalBase a s Ω initial)
    (preparedExecutionTerminal a s Ω (preparedRejectedCorrectedExecution a s Ω initial K L)) = ∅
  rw [same]
  ext L
  simp [preparedCapabilityLoss, preparedExecutionTerminal, preparedOriginalHistoryRun,
    preparedHistoryRun, preparedHistoryInitial]

end
end AASCKleinGordon
