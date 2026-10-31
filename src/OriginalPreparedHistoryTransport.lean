import OriginalPreparedFailureHistory

/-! Derive operation congruence on actual prepared histories. A frame is a
presentation of the same original prepared use; source, current full original
use and computed event history are all retained. No preservation field is an
input, and no scalar/tensor profile replaces the complete original use. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def PreparedHistorySame (x y : PreparedHistoryState a s Ω) : Prop :=
  x.source = y.source ∧ preparedOriginalBase a s Ω x.locus = preparedOriginalBase a s Ω y.locus ∧
    x.events = y.events

theorem prepared_history_vary_base (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω) :
    preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus =
      if inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
          (preparedOriginalBase a s Ω x.locus)).val+K ∈ wickOriginalMetricNeighborhood Ω then
        preparedReplaceAct a s Ω (preparedOriginalBase a s Ω x.locus)
          ((originalEHPreparedAct s Ω (kgOriginalObject a)
            (preparedOriginalBase a s Ω x.locus)).val+K) inside
      else preparedOriginalBase a s Ω x.locus := by
  classical
  unfold preparedHistoryVary
  dsimp only
  split
  · exact prepared_original_base_in_frame a s Ω _ _
  · rfl

theorem prepared_history_vary_admitted (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∈ wickOriginalMetricNeighborhood Ω) :
    preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus =
      preparedReplaceAct a s Ω (preparedOriginalBase a s Ω x.locus)
        ((originalEHPreparedAct s Ω (kgOriginalObject a)
          (preparedOriginalBase a s Ω x.locus)).val+K) inside := by
  rw [prepared_history_vary_base,dif_pos inside]

theorem prepared_history_vary_rejected (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (outside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∉ wickOriginalMetricNeighborhood Ω) :
    preparedHistoryVary a s Ω K x =
      preparedHistoryObserve a s Ω (preparedFiniteRequest a Ω
        ((originalEHPreparedAct s Ω (kgOriginalObject a)
          (preparedOriginalBase a s Ω x.locus)).val+K)) x := by
  classical
  unfold preparedHistoryVary
  dsimp only
  rw [dif_neg outside]

theorem prepared_history_step_congruence (operation : PreparedHistoryOperation a Ω)
    (x y : PreparedHistoryState a s Ω) (same : PreparedHistorySame a s Ω x y) :
    PreparedHistorySame a s Ω (preparedHistoryStep a s Ω operation x)
      (preparedHistoryStep a s Ω operation y) := by
  classical
  obtain ⟨source,base,events⟩ := same
  refine ⟨(prepared_history_step_source a s Ω operation x).trans
    (source.trans (prepared_history_step_source a s Ω operation y).symm),?_,?_⟩
  · cases operation with
    | observe π => exact base
    | frame q =>
      exact (prepared_original_base_frame_change a s Ω q x.locus).trans
        (base.trans (prepared_original_base_frame_change a s Ω q y.locus).symm)
    | vary K =>
      change preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus =
        preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K y).locus
      rw [prepared_history_vary_base,prepared_history_vary_base]
      simp only [base]
  · cases operation with
    | observe π =>
      change x.events ++ [⟨preparedOriginalBase a s Ω x.locus,π⟩] =
        y.events ++ [⟨preparedOriginalBase a s Ω y.locus,π⟩]
      rw [events,base]
    | frame q => exact events
    | vary K =>
      change (preparedHistoryVary a s Ω K x).events = (preparedHistoryVary a s Ω K y).events
      rw [prepared_history_vary_events,prepared_history_vary_events,events,base]

theorem prepared_history_run_congruence (operations : List (PreparedHistoryOperation a Ω))
    (x y : PreparedHistoryState a s Ω) (same : PreparedHistorySame a s Ω x y) :
    PreparedHistorySame a s Ω (preparedHistoryRun a s Ω operations x)
      (preparedHistoryRun a s Ω operations y) := by
  induction operations generalizing x y with
  | nil => exact same
  | cons operation rest ih =>
    exact ih _ _ (prepared_history_step_congruence a s Ω operation x y same)

theorem prepared_history_frame_same (q : ProperPoincareTransform) (x : PreparedHistoryState a s Ω) :
    PreparedHistorySame a s Ω (preparedHistoryFrame a s Ω q x) x :=
  ⟨rfl,prepared_original_base_frame_change a s Ω q x.locus,rfl⟩

theorem prepared_history_same_original_references (x y : PreparedHistoryState a s Ω)
    (same : PreparedHistorySame a s Ω x y) (π : PreparedQuestion a Ω) :
    (kgJointFrameFamilyReferences s Ω (kgOriginalObject a)).referenceAt x.locus π =
      (kgJointFrameFamilyReferences s Ω (kgOriginalObject a)).referenceAt y.locus π :=
  (original_eh_joint_frame_profile_iff_original s Ω (kgOriginalObject a) x.locus y.locus).mpr same.2.1 π

theorem prepared_history_same_eh_evaluators (κ Λ : ℝ) (x y : PreparedHistoryState a s Ω)
    (same : PreparedHistorySame a s Ω x y) :
    (originalEHJointFrameUse s Ω (kgOriginalObject a) κ Λ x.locus.1 x.locus.2).2 =
      (originalEHJointFrameUse s Ω (kgOriginalObject a) κ Λ y.locus.1 y.locus.2).2 := by
  have left := original_eh_joint_frame_evaluator s Ω (kgOriginalObject a) κ Λ x.locus.1
    (preparedOriginalBase a s Ω x.locus)
  have right := original_eh_joint_frame_evaluator s Ω (kgOriginalObject a) κ Λ y.locus.1
    (preparedOriginalBase a s Ω y.locus)
  simp only [preparedOriginalBase,originalEHJointFrameOriginal,Equiv.apply_symm_apply] at left right
  exact left.trans ((congrArg (fun z => (originalEHPreparedUse s Ω (kgOriginalObject a) κ Λ z).2)
    same.2.1).trans right.symm)

theorem prepared_history_rejected_event_reason (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (outside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∉ wickOriginalMetricNeighborhood Ω) :
    preparedEventFailure a s Ω
      ⟨preparedOriginalBase a s Ω x.locus,preparedFiniteRequest a Ω
        ((originalEHPreparedAct s Ω (kgOriginalObject a)
          (preparedOriginalBase a s Ω x.locus)).val+K)⟩ = some .originalMetricRejection := by
  rw [prepared_finite_request_failure,if_neg outside]

theorem prepared_history_eh_admitted_after_rejection (κ Λ : ℝ) (coupling : κ ≠ 0)
    (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (outside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val+K ∉ wickOriginalMetricNeighborhood Ω) :
    preparedEventFailure a s Ω
      ⟨preparedOriginalBase a s Ω x.locus,preparedFiniteRequest a Ω
        ((originalEHPreparedAct s Ω (kgOriginalObject a)
          (preparedOriginalBase a s Ω x.locus)).val+K)⟩ = some .originalMetricRejection ∧
    ∃ v,(originalEHPreparedUse s Ω (kgOriginalObject a) κ Λ
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus)).2 = some v := by
  refine ⟨prepared_history_rejected_event_reason a s Ω K x outside,?_⟩
  exact ⟨_,original_eh_prepared_evaluation s Ω (kgOriginalObject a) κ Λ coupling _⟩

end
end AASCKleinGordon
