import OriginalPreparedContinuationSeparation

/-! Concrete pre/disturbed/restored planned-use capability on the same original
prepared carrier. This is a component relevant to R2 Proposition6.3, not its full
standing-bearing role interpretation. The selected states remain admitted.
Different computed request occurrences are never identified as the same act. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def preparedNextVariationEvent (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω) :
    PreparedEvent a s Ω :=
  ⟨preparedOriginalBase a s Ω x.locus,preparedFiniteRequest a Ω
    ((originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K)⟩

theorem prepared_next_variation_actual_event (K : MetricSourceProbe Ω)
    (x : PreparedHistoryState a s Ω) :
    (preparedHistoryVary a s Ω K x).events = x.events ++ [preparedNextVariationEvent a s Ω K x] :=
  prepared_history_vary_events a s Ω K x

theorem prepared_planned_use_capability_threat_and_correction
    (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ L : MetricSourceProbe Ω,
      preparedEventFailure a s Ω (preparedNextVariationEvent a s Ω L x) = none ∧
      preparedEventFailure a s Ω
        (preparedNextVariationEvent a s Ω L (preparedHistoryVary a s Ω K x)) =
          some .originalMetricRejection ∧
      preparedEventFailure a s Ω (preparedNextVariationEvent a s Ω L
        (preparedHistoryVary a s Ω (-K) (preparedHistoryVary a s Ω K x))) = none ∧
      preparedOriginalBase a s Ω
        (preparedHistoryVary a s Ω (-K) (preparedHistoryVary a s Ω K x)).locus =
          preparedOriginalBase a s Ω x.locus ∧
      kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
        (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) =
          kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
            (preparedOriginalBase a s Ω x.locus) ∧
      kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω)
        (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) =
          kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω)
            (preparedOriginalBase a s Ω x.locus) := by
  obtain ⟨L,left,right⟩ :=
    prepared_history_same_next_variation_separates_original_requests a s Ω K nonzero x inside
  refine ⟨L,left,right,?_,prepared_history_restore_base a s Ω K x inside,
    prepared_history_vary_quantum_unchanged a s Ω K x,
    prepared_history_vary_original_attachment_unchanged a s Ω K x⟩
  unfold preparedNextVariationEvent
  rw [prepared_history_restore_base a s Ω K x inside]
  exact left

theorem prepared_recorded_rejection_retained_after_operand_correction
    (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ L : MetricSourceProbe Ω,
      let disturbed := preparedHistoryVary a s Ω K x
      let rejected := preparedHistoryVary a s Ω L disturbed
      let corrected := preparedHistoryVary a s Ω (-K) rejected
      let failedEvent := preparedNextVariationEvent a s Ω L disturbed
      preparedEventFailure a s Ω failedEvent = some .originalMetricRejection ∧
      failedEvent ∈ corrected.events ∧ preparedEventAnswer a s Ω failedEvent = none ∧
      preparedOriginalBase a s Ω corrected.locus = preparedOriginalBase a s Ω x.locus ∧
      ∃ v,preparedEventAnswer a s Ω (preparedNextVariationEvent a s Ω L corrected) = some v := by
  obtain ⟨L,left,right⟩ := prepared_metric_original_boundary_separates_translation Ω
    (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).val
    K (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedOriginalBase a s Ω x.locus)).property nonzero
  refine ⟨L,?_⟩
  dsimp only
  let disturbed := preparedHistoryVary a s Ω K x
  let rejected := preparedHistoryVary a s Ω L disturbed
  let corrected := preparedHistoryVary a s Ω (-K) rejected
  let failedEvent := preparedNextVariationEvent a s Ω L disturbed
  have outside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω disturbed.locus)).val+L ∉ wickOriginalMetricNeighborhood Ω := by
    rw [prepared_history_vary_operand a s Ω K x inside]
    exact right
  have failure : preparedEventFailure a s Ω failedEvent = some .originalMetricRejection := by
    exact prepared_history_rejected_event_reason a s Ω L disturbed outside
  have present : failedEvent ∈ rejected.events := by
    change failedEvent ∈ (preparedHistoryVary a s Ω L disturbed).events
    rw [prepared_next_variation_actual_event]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have retained := prepared_history_original_failed_locus_retained a s Ω [.vary (-K)]
    rejected failedEvent present .originalMetricRejection failure
  have rejectedBase : preparedOriginalBase a s Ω rejected.locus =
      preparedOriginalBase a s Ω disturbed.locus := by
    change preparedOriginalBase a s Ω (preparedHistoryVary a s Ω L disturbed).locus = _
    rw [prepared_history_vary_rejected a s Ω L disturbed outside]
    rfl
  have restored : preparedOriginalBase a s Ω corrected.locus =
      preparedOriginalBase a s Ω x.locus := by
    calc
      _ = preparedOriginalBase a s Ω
          (preparedHistoryVary a s Ω (-K) disturbed).locus := by
        change preparedOriginalBase a s Ω (preparedHistoryVary a s Ω (-K) rejected).locus = _
        rw [prepared_history_vary_base a s Ω (-K) rejected,
          prepared_history_vary_base a s Ω (-K) disturbed,rejectedBase]
      _ = _ := prepared_history_restore_base a s Ω K x inside
  refine ⟨failure,retained.1,retained.2,restored,?_⟩
  unfold preparedNextVariationEvent
  rw [restored]
  exact (prepared_finite_request_admission_exact a s Ω _ _).mpr left

end
end AASCKleinGordon
