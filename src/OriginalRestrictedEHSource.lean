import OriginalRestrictedResponseDescent

/-! Actual original EH directional uses on the retained raw-history source.
The observation differentiates the computed operand H+tK, before any source
profile quotient is introduced. The same old preparation, failure records
and declared continuation repertoire remain available in the full response.
No two-parameter, Hadamard or arbitrary-curve regularity is claimed. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace Filter MeasureTheory
open scoped Topology
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def restrictedEHResponseEquiv : RestrictedOriginalResponse a s Ω ≃ PreparedHistoryReceiver a s Ω :=
  Equiv.ofBijective (restrictedOriginalResponseReceive a s Ω)
    (restricted_original_response_receive_bijective a s Ω)

def restrictedEHPrepared (q : RestrictedOriginalResponse a s Ω) : PreparedOriginal a s Ω :=
  preparedExecutionProjection a s Ω (restrictedEHResponseEquiv a s Ω q)

def restrictedEHAct (q : RestrictedOriginalResponse a s Ω) :=
  originalEHPreparedAct s Ω (kgOriginalObject a) (restrictedEHPrepared a s Ω q)

def restrictedEHMetric (q : RestrictedOriginalResponse a s Ω) : MetricField :=
  originalEHPreparedMetric s Ω (kgOriginalObject a) (restrictedEHPrepared a s Ω q)

theorem restricted_eh_raw_current (h : RestrictedRawHistory a Ω) :
    restrictedEHPrepared a s Ω (Quotient.mk _ h) =
      restrictedRawReceive a s Ω (restrictedRawHistoryRun a Ω h).current :=
  (restricted_raw_history_run_matches a s Ω h).2.1.symm

theorem restricted_eh_prepared_coverage (frame : ProperPoincareTransform) :
    Function.Surjective (restrictedEHPrepared a s Ω) := by
  intro z
  obtain ⟨y, hy⟩ := prepared_execution_projection_onto_old_carrier a s Ω frame z
  obtain ⟨q, hq⟩ := (restrictedEHResponseEquiv a s Ω).surjective y
  exact ⟨q, (congrArg (preparedExecutionProjection a s Ω) hq).trans hy⟩

def restrictedRawEHObserve (κ Λ : ℝ) (h : RestrictedRawHistory a Ω) (K : MetricSourceProbe Ω) : ℝ :=
  deriv (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
    ((restrictedRawHistoryRun a Ω h).current.act.val + t • K)) 0

def restrictedEHObserve (κ Λ : ℝ) (q : RestrictedOriginalResponse a s Ω) (K : MetricSourceProbe Ω) : ℝ :=
  deriv (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
    ((restrictedEHAct a s Ω q).val + t • K)) 0

theorem restricted_eh_raw_observation_square (κ Λ : ℝ) (h : RestrictedRawHistory a Ω)
    (K : MetricSourceProbe Ω) :
    restrictedRawEHObserve a Ω κ Λ h K =
      restrictedEHObserve a s Ω κ Λ (Quotient.mk _ h) K := by
  unfold restrictedEHObserve restrictedEHAct
  rw [restricted_eh_raw_current]
  rfl

def restrictedEHVariation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  originalEHPreparedFirstVariation s Ω (kgOriginalObject a) κ Λ coupling
    (restrictedEHPrepared a s Ω q)

def restrictedEHSource (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) : SymmetricSourceComponents Ω :=
  representedMetricSource (restrictedEHVariation a s Ω κ Λ coupling q)

theorem restricted_eh_actual_derivative (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) (K : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
      ((restrictedEHAct a s Ω q).val + t • K))
      (restrictedEHVariation a s Ω κ Λ coupling q K) 0 := by
  exact original_eh_actual_act_hasDerivAt κ Λ coupling
    (restrictedEHAct a s Ω q).val (restrictedEHAct a s Ω q).property K

theorem restricted_eh_observation_is_actual_variation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) (K : MetricSourceProbe Ω) :
    restrictedEHObserve a s Ω κ Λ q K = restrictedEHVariation a s Ω κ Λ coupling q K :=
  (restricted_eh_actual_derivative a s Ω κ Λ coupling q K).deriv

theorem restricted_eh_raw_comparison_preserves_observation (κ Λ : ℝ)
    (h k : RestrictedRawHistory a Ω) (same : RestrictedRawProgramSame a s Ω h k)
    (K : MetricSourceProbe Ω) :
    restrictedRawEHObserve a Ω κ Λ h K = restrictedRawEHObserve a Ω κ Λ k K := by
  rw [restricted_eh_raw_observation_square a s Ω, restricted_eh_raw_observation_square a s Ω]
  exact congrArg (fun q => restrictedEHObserve a s Ω κ Λ q K) (Quotient.sound same)

theorem restricted_eh_source_half_pairing (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) (K : MetricSourceProbe Ω) :
    (1/2 : ℝ) * metricSourcePairing (restrictedEHSource a s Ω κ Λ coupling q) K =
      restrictedEHObserve a s Ω κ Λ q K := by
  rw [restricted_eh_observation_is_actual_variation]
  exact constructed_metric_source_represents _ K

theorem restricted_eh_same_metric_source_density (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    restrictedEHSource a s Ω κ Λ coupling q i φ =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (restrictedEHMetric a s Ω q)
        (originalEHGeometricResponse κ Λ (restrictedEHMetric a s Ω q))) i p * φ p :=
  original_eh_prepared_euler_same_metric_density s Ω (kgOriginalObject a) κ Λ coupling
    (restrictedEHPrepared a s Ω q) i φ

theorem restricted_eh_actual_direction_admitted (q : RestrictedOriginalResponse a s Ω)
    (K : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0, (restrictedEHAct a s Ω q).val + t • K ∈ wickOriginalMetricNeighborhood Ω :=
  original_eh_actual_act_curve_admitted _ (restrictedEHAct a s Ω q).property K

theorem restricted_eh_finite_readout_admitted (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) :
    (originalEHPreparedUse s Ω (kgOriginalObject a) κ Λ (restrictedEHPrepared a s Ω q)).2 =
      some (originalEHRelativeAction κ Λ wickNativeFlatMetric (restrictedEHAct a s Ω q).val) :=
  original_eh_prepared_evaluation s Ω (kgOriginalObject a) κ Λ coupling _

theorem restricted_eh_continuation_current (ops : List (PreparedHistoryOperation a Ω))
    (q : RestrictedOriginalResponse a s Ω) :
    restrictedEHPrepared a s Ω (restrictedOriginalResponseContinue a s Ω ops q) =
      preparedOriginalProgram a s Ω ops (restrictedEHPrepared a s Ω q) := by
  change preparedExecutionProjection a s Ω
    (restrictedOriginalResponseReceive a s Ω (restrictedOriginalResponseContinue a s Ω ops q)) = _
  rw [restricted_original_response_continuation_square, prepared_execution_program_projection_square]
  rfl

theorem restricted_eh_variation_failure_exact (K : MetricSourceProbe Ω)
    (q : RestrictedOriginalResponse a s Ω) :
    preparedOriginalOperationFailure a s Ω (.vary K) (restrictedEHPrepared a s Ω q) =
      if (restrictedEHAct a s Ω q).val + K ∈ wickOriginalMetricNeighborhood Ω then
        none else some .originalMetricRejection :=
  prepared_finite_request_failure a s Ω (restrictedEHPrepared a s Ω q) _

theorem restricted_eh_original_failure_retained (ops : List (PreparedHistoryOperation a Ω))
    (q : RestrictedOriginalResponse a s Ω) (n : ℕ) (reason : KGExecutionFailure)
    (failed : preparedHistoryReadFirstFailure a s Ω (restrictedOriginalResponseReceive a s Ω q) =
      some (n, reason)) :
    preparedHistoryReadFirstFailure a s Ω
      (restrictedOriginalResponseReceive a s Ω (restrictedOriginalResponseContinue a s Ω ops q)) =
      some (n, reason) := by
  rw [restricted_original_response_continuation_square]
  exact prepared_history_quotient_first_failure_retained a s Ω ops _ n reason failed

end
end AASCKleinGordon
