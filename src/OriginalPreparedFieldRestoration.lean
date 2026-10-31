import OriginalPreparedUseBoundary
import OriginalPreparedRestoration

/-! Actual field/identity/restoration components, not a literal-trace proxy.
The original field reference detects every nonzero admitted metric change.
The preparation's quantum/source component and old question definedness remain
fixed. These computations do not identify the full R2 charged repair role. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem prepared_replace_field_exact (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z H inside) = wickOriginalFiniteMetric H := by
  rw [kg_prepared_metric_field_eq]
  exact congrArg wickOriginalFiniteMetric (prepared_replace_actual_operand a s Ω z H inside)

theorem prepared_replace_field_unchanged_iff (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z H inside) =
        kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z ↔
      H = (originalEHPreparedAct s Ω (kgOriginalObject a) z).val := by
  rw [prepared_replace_field_exact,kg_prepared_metric_field_eq]
  exact (kg_finite_metric_test_injective Ω).eq_iff

theorem prepared_replace_field_addition (z : PreparedOriginal a s Ω)
    (K : MetricSourceProbe Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K ∈
      wickOriginalMetricNeighborhood Ω) (p : Spacetime) :
    kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z
        ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K) inside) p =
      kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z p +
        wickNativeMetricVariation K p := by
  rw [prepared_replace_field_exact,kg_prepared_metric_field_eq]
  change wickFlatMetric + tensorEncodeLinear
      ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val (wickSpacetimeCoordinates p) +
        K (wickSpacetimeCoordinates p)) =
    (wickFlatMetric + tensorEncodeLinear
      ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val (wickSpacetimeCoordinates p))) +
        tensorEncodeLinear (K (wickSpacetimeCoordinates p))
  rw [map_add,add_assoc]

theorem prepared_replace_field_off_support (z : PreparedOriginal a s Ω)
    (K : MetricSourceProbe Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K ∈
      wickOriginalMetricNeighborhood Ω) (p : Spacetime)
    (outside : p ∉ tsupport (wickNativeMetricVariation K)) :
    kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z
        ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val + K) inside) p =
      kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z p := by
  rw [prepared_replace_field_addition,image_eq_zero_of_notMem_tsupport outside,add_zero]

theorem prepared_replace_actual_field_reference_changed (z : PreparedOriginal a s Ω)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (different : H ≠ (originalEHPreparedAct s Ω (kgOriginalObject a) z).val) :
    ∃ (p : Spacetime) (i j : Fin 4),
      preparedEventAnswer a s Ω
        ⟨preparedReplaceAct a s Ω z H inside,.inl (p,kgJointFrameMatrixEntry i j)⟩ ≠
      preparedEventAnswer a s Ω ⟨z,.inl (p,kgJointFrameMatrixEntry i j)⟩ := by
  by_contra! same
  apply different
  apply (prepared_replace_field_unchanged_iff a s Ω z H inside).mp
  funext p i j
  have h := same p i j
  change some (Sum.inl
    (kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z H inside) p i j)) =
      some (Sum.inl
        (kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z p i j)) at h
  exact Sum.inl.inj (Option.some.inj h)

theorem prepared_history_nonzero_variation_changes_actual_field
    (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    ∃ (p : Spacetime) (i j : Fin 4),
      preparedEventAnswer a s Ω
        ⟨preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus,
          .inl (p,kgJointFrameMatrixEntry i j)⟩ ≠
      preparedEventAnswer a s Ω
        ⟨preparedOriginalBase a s Ω x.locus,.inl (p,kgJointFrameMatrixEntry i j)⟩ := by
  rw [prepared_history_vary_admitted a s Ω K x inside]
  apply prepared_replace_actual_field_reference_changed
  intro same
  apply nonzero
  exact add_left_cancel (same.trans (add_zero _).symm)

theorem prepared_history_vary_quantum_unchanged (K : MetricSourceProbe Ω)
    (x : PreparedHistoryState a s Ω) :
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) =
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus) := by
  rw [prepared_history_vary_base]
  split
  · exact prepared_replace_quantum a s Ω _ _ _
  · rfl

theorem prepared_history_vary_original_attachment_unchanged (K : MetricSourceProbe Ω)
    (x : PreparedHistoryState a s Ω) :
    kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω)
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) =
    kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω)
      (preparedOriginalBase a s Ω x.locus) := by
  unfold kgPreparedOriginalAttachment kgPreparedOriginalRecord
  rw [prepared_history_vary_quantum_unchanged]

theorem prepared_history_vary_all_question_admission_unchanged
    (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω) (π : PreparedQuestion a Ω) :
    (∃ v,preparedEventAnswer a s Ω
      ⟨preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus,π⟩ = some v) ↔
      ∃ v,preparedEventAnswer a s Ω ⟨preparedOriginalBase a s Ω x.locus,π⟩ = some v := by
  rw [prepared_history_vary_base]
  split
  · exact prepared_replace_all_question_admission a s Ω _ _ _ π
  · rfl

theorem prepared_history_inverse_restores_all_original_answers
    (K : MetricSourceProbe Ω) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val + K ∈ wickOriginalMetricNeighborhood Ω)
    (π : PreparedQuestion a Ω) :
    preparedEventAnswer a s Ω
      ⟨preparedOriginalBase a s Ω
        (preparedHistoryVary a s Ω (-K) (preparedHistoryVary a s Ω K x)).locus,π⟩ =
      preparedEventAnswer a s Ω ⟨preparedOriginalBase a s Ω x.locus,π⟩ := by
  rw [prepared_history_restore_base a s Ω K x inside]

end
end AASCKleinGordon
