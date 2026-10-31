import OriginalPreparedProtocolStep

/-! Exact use-boundary tests on the SAME original prepared carrier. An admitted
operand replacement preserves the registered preparation references, while
metric-field values may change. Equality of admission profiles does not identify
the full physical role or the source's standing-localization quotient. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem prepared_replace_registered_reference (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (π : RegisteredQuestion
      (KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a))) :
    kgJointFrameOriginalAnswer s Ω (kgOriginalObject a)
      (preparedReplaceAct a s Ω z H inside) (.inr π) =
        kgJointFrameOriginalAnswer s Ω (kgOriginalObject a) z (.inr π) := by
  change (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)).referenceAt
      (preparedReplaceAct a s Ω z H inside) (.inr π) = _
  rw [kg_prepared_registered_standing_square,prepared_replace_quantum]
  exact (kg_prepared_registered_standing_square s Ω (wickOriginalMetricNeighborhood Ω)
    (kgOriginalObject a) z π).symm

theorem prepared_replace_typed_failure (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (π : PreparedQuestion a Ω) :
    preparedEventFailure a s Ω ⟨preparedReplaceAct a s Ω z H inside,π⟩ =
      preparedEventFailure a s Ω ⟨z,π⟩ := by
  cases π with
  | inl test => rfl
  | inr π =>
    cases π with
    | ledger π => rfl
    | execution π =>
      change kgExecutionFailureOf
        (kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
          (preparedReplaceAct a s Ω z H inside) π) = _
      rw [prepared_replace_original_record]
      rfl

theorem prepared_replace_all_question_admission (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (π : PreparedQuestion a Ω) :
    (∃ v,preparedEventAnswer a s Ω ⟨preparedReplaceAct a s Ω z H inside,π⟩ = some v) ↔
      ∃ v,preparedEventAnswer a s Ω ⟨z,π⟩ = some v := by
  rw [prepared_event_answer_guard,prepared_event_answer_guard,prepared_replace_typed_failure]
  split <;> simp

theorem prepared_replace_all_question_failure (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (π : PreparedQuestion a Ω) :
    preparedEventAnswer a s Ω ⟨preparedReplaceAct a s Ω z H inside,π⟩ = none ↔
      preparedEventAnswer a s Ω ⟨z,π⟩ = none := by
  rw [prepared_event_failure_exact,prepared_event_failure_exact,prepared_replace_typed_failure]

theorem prepared_finite_request_diagnostic_origin_independent
    (z w : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω) :
    preparedEventFailure a s Ω ⟨z,preparedFiniteRequest a Ω H⟩ =
      preparedEventFailure a s Ω ⟨w,preparedFiniteRequest a Ω H⟩ := by
  rw [prepared_finite_request_failure,prepared_finite_request_failure]

theorem prepared_replace_original_attachment (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω)
      (preparedReplaceAct a s Ω z H inside) =
        kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω) z := by
  unfold kgPreparedOriginalAttachment kgPreparedOriginalRecord
  rw [prepared_replace_quantum]

theorem prepared_replace_original_source_ledger (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedOriginalSourceLedger a s Ω (wickOriginalMetricNeighborhood Ω)
      (preparedReplaceAct a s Ω z H inside) =
        kgPreparedOriginalSourceLedger a s Ω (wickOriginalMetricNeighborhood Ω) z := by
  unfold kgPreparedOriginalSourceLedger kgPreparedOriginalRecord
  rw [prepared_replace_quantum]

end
end AASCKleinGordon
