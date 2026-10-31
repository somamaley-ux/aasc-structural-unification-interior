import OriginalPreparedHistoryTransport

/-! Actual admitted operand restoration and retained original failure. A
closed operand cycle restores the existing prepared use but not its history.
This is not an identification of the whole R2 repair-window/burden calculus. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace Filter
open scoped Topology
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem prepared_history_vary_operand (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∈ wickOriginalMetricNeighborhood Ω) :
    (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus)).val =
      (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).val+K := by
  rw [prepared_history_vary_admitted a s Ω K x inside,prepared_replace_actual_operand]

theorem prepared_history_small_variations (x : PreparedHistoryState a s Ω) (K : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0,
      (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).val+t•K ∈
        wickOriginalMetricNeighborhood Ω :=
  original_eh_actual_act_curve_admitted _
    (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).property K

theorem prepared_history_restore_base (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∈ wickOriginalMetricNeighborhood Ω) :
    preparedOriginalBase a s Ω
      (preparedHistoryVary a s Ω (-K) (preparedHistoryVary a s Ω K x)).locus =
      preparedOriginalBase a s Ω x.locus := by
  let z := preparedOriginalBase a s Ω x.locus
  let H := originalEHPreparedAct s Ω (kgOriginalObject a) z
  have operand := prepared_history_vary_operand a s Ω K x inside
  have cancel : H.val+K+-K = H.val := add_neg_cancel_right H.val K
  calc
    _ = preparedReplaceAct a s Ω (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus)
        H.val H.property := by
      rw [prepared_history_vary_base,operand]
      simp only [show (originalEHPreparedAct s Ω (kgOriginalObject a)
        (preparedOriginalBase a s Ω x.locus)).val+K+-K = H.val from cancel,dif_pos H.property]
    _ = preparedReplaceAct a s Ω (preparedReplaceAct a s Ω z (H.val+K) inside) H.val H.property :=
      congrArg (fun w => preparedReplaceAct a s Ω w H.val H.property)
        (prepared_history_vary_admitted a s Ω K x inside)
    _ = preparedReplaceAct a s Ω z H.val H.property := prepared_replace_twice a s Ω z _ _ inside H.property
    _ = z := prepared_replace_original a s Ω z

theorem prepared_history_restore_event_count (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω) :
    (preparedHistoryVary a s Ω (-K) (preparedHistoryVary a s Ω K x)).events.length =
      x.events.length+2 := by
  rw [prepared_history_vary_events,prepared_history_vary_events]
  simp [List.length_append]

theorem prepared_history_restoration_is_not_history_erasure (K : MetricSourceProbe Ω)
    (x : PreparedHistoryState a s Ω) :
    ¬ PreparedHistorySame a s Ω
      (preparedHistoryVary a s Ω (-K) (preparedHistoryVary a s Ω K x)) x := by
  intro same
  have length := congrArg List.length same.2.2
  rw [prepared_history_restore_event_count] at length
  exact (Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0<2))) length

theorem prepared_history_original_failed_locus_retained
    (operations : List (PreparedHistoryOperation a Ω)) (x : PreparedHistoryState a s Ω)
    (e : PreparedEvent a s Ω) (present : e ∈ x.events)
    (reason : KGExecutionFailure) (failed : preparedEventFailure a s Ω e = some reason) :
    e ∈ (preparedHistoryRun a s Ω operations x).events ∧ preparedEventAnswer a s Ω e = none := by
  obtain ⟨tail,htail⟩ := prepared_history_run_events_prefix a s Ω operations x
  constructor
  · rw [htail]
    exact List.mem_append_left tail present
  · apply (prepared_event_failure_exact a s Ω e).mpr
    rw [failed]
    exact Option.some_ne_none reason

theorem prepared_history_rejection_first_failure (K : MetricSourceProbe Ω)
    (x : PreparedHistoryState a s Ω)
    (before : preparedHistoryFirstFailure a s Ω x.events = none)
    (outside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∉ wickOriginalMetricNeighborhood Ω) :
    preparedHistoryFirstFailure a s Ω (preparedHistoryVary a s Ω K x).events =
      some (x.events.length,KGExecutionFailure.originalMetricRejection) := by
  rw [prepared_history_vary_events,prepared_history_first_failure_append,before]
  simp only [preparedHistoryFirstFailure,prepared_history_rejected_event_reason a s Ω K x outside,
    Option.map,zero_add]

theorem prepared_history_rejection_cannot_be_repaired_retroactively
    (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (before : preparedHistoryFirstFailure a s Ω x.events = none)
    (outside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∉ wickOriginalMetricNeighborhood Ω)
    (later : List (PreparedHistoryOperation a Ω)) :
    preparedHistoryFirstFailure a s Ω
      (preparedHistoryRun a s Ω later (preparedHistoryVary a s Ω K x)).events =
        some (x.events.length,KGExecutionFailure.originalMetricRejection) :=
  prepared_history_first_failure_retained a s Ω later _ _ _
    (prepared_history_rejection_first_failure a s Ω K x before outside)

end
end AASCKleinGordon
