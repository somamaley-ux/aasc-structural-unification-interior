import OriginalEHPreparedAttachment

/-! Differentiate the actual EH readout on the ORIGINAL admitted metric-act
curve H+tK. The action cocycle is derived using integrability, not received as
a bridge. The same prepared quantum record is retained along this act curve.
-/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace MeasureTheory Filter
open scoped Topology

variable {Ω : Opens CoordinatePoint}

theorem original_eh_act_additive_perturbation (H K : MetricSourceProbe Ω) :
    originalEHMetricPerturbation (originalEHActMetric H) K = originalEHActMetric (H+K) := by
  funext p i j
  have encoded := congrArg (fun M : Tensor2 => M i j) (tensorEncodeLinear.map_add (H p) (K p))
  change tensorEncode (H p + K p) i j = tensorEncode (H p) i j + tensorEncode (K p) i j at encoded
  change (wickFlatMetric i j + tensorEncode (H p) i j) + tensorEncode (K p) i j =
    wickFlatMetric i j + tensorEncode (H p + K p) i j
  rw [encoded]
  ring

theorem original_eh_actual_act_curve_admitted (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) (K : MetricSourceProbe Ω) :
    ∀ᶠ t : ℝ in 𝓝 0, H+t•K ∈ wickOriginalMetricNeighborhood Ω := by
  have continuousCurve : Continuous (fun t : ℝ => H+t•K) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have atZero : H+(0:ℝ)•K ∈ wickOriginalMetricNeighborhood Ω := by simpa using inside
  exact continuousCurve.continuousAt ((wick_original_metric_neighborhood_open Ω).mem_nhds atZero)

theorem original_eh_action_cocycle (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H K : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (next : H+K ∈ wickOriginalMetricNeighborhood Ω) :
    originalEHRelativeAction κ Λ (originalEHActMetric H) K =
      originalEHRelativeAction κ Λ wickNativeFlatMetric (H+K) -
        originalEHRelativeAction κ Λ wickNativeFlatMetric H := by
  have currentIntegrable := (original_eh_original_act_admitted κ Λ coupling H inside).2.2.2
  have nextIntegrable := (original_eh_original_act_admitted κ Λ coupling (H+K) next).2.2.2
  have integrand : originalEHRelativeIntegrand κ Λ (originalEHActMetric H) K =
      fun p => originalEHRelativeIntegrand κ Λ wickNativeFlatMetric (H+K) p -
        originalEHRelativeIntegrand κ Λ wickNativeFlatMetric H p := by
    funext p
    unfold originalEHRelativeIntegrand
    rw [original_eh_act_additive_perturbation]
    change originalEHScalarDensity κ Λ (originalEHActMetric (H+K)) p -
      originalEHScalarDensity κ Λ (originalEHActMetric H) p =
      (originalEHScalarDensity κ Λ (originalEHActMetric (H+K)) p - originalEHScalarDensity κ Λ wickNativeFlatMetric p) -
      (originalEHScalarDensity κ Λ (originalEHActMetric H) p - originalEHScalarDensity κ Λ wickNativeFlatMetric p)
    ring
  unfold originalEHRelativeAction
  rw [integrand,integral_sub nextIntegrable currentIntegrable]

theorem original_eh_actual_act_hasDerivAt (κ Λ : ℝ) (coupling : κ ≠ 0)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (K : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric (H+t•K))
      ((originalEHFirstVariation κ Λ coupling (originalEHActMetric H)
        (original_eh_act_metric_symmetric H) (original_eh_act_metric_smooth H)
        (fun p _ => original_eh_act_metric_negative H inside p)) K) 0 := by
  have variation := eh_original_first_variation_hasDerivAt κ Λ coupling (originalEHActMetric H)
    (original_eh_act_metric_symmetric H) (original_eh_act_metric_smooth H)
    (fun p (_ : p ∈ Ω) => original_eh_act_metric_negative H inside p) K
  apply (variation.add_const (originalEHRelativeAction κ Λ wickNativeFlatMetric H)).congr_of_eventuallyEq
  filter_upwards [original_eh_actual_act_curve_admitted H inside K] with t ht
  rw [original_eh_action_cocycle κ Λ coupling H (t•K) inside ht]
  ring

variable {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint) (A : KGFamilyObject a)

def originalEHPreparedActCurve (x : OriginalEHPreparedUse s Ω A) (K : MetricSourceProbe Ω)
    (t : ℝ) (inside : (originalEHPreparedAct s Ω A x).val+t•K ∈ wickOriginalMetricNeighborhood Ω) :
    OriginalEHPreparedUse s Ω A :=
  kgPreparedUseOfRayAct s Ω (wickOriginalMetricNeighborhood Ω) A
    ⟨(originalEHPreparedAct s Ω A x).val+t•K,inside⟩
    (kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) A x)

theorem original_eh_prepared_curve_actual_operand (x : OriginalEHPreparedUse s Ω A)
    (K : MetricSourceProbe Ω) (t : ℝ)
    (inside : (originalEHPreparedAct s Ω A x).val+t•K ∈ wickOriginalMetricNeighborhood Ω) :
    (originalEHPreparedAct s Ω A (originalEHPreparedActCurve s Ω A x K t inside)).val =
      (originalEHPreparedAct s Ω A x).val+t•K := by
  induction x using Quotient.inductionOn with | _ x => rfl

theorem original_eh_prepared_curve_original_record (x : OriginalEHPreparedUse s Ω A)
    (K : MetricSourceProbe Ω) (t : ℝ)
    (inside : (originalEHPreparedAct s Ω A x).val+t•K ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) A
      (originalEHPreparedActCurve s Ω A x K t inside) =
        kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) A x := by
  induction x using Quotient.inductionOn with | _ x => rfl

theorem original_eh_prepared_curve_registered_reference (x : OriginalEHPreparedUse s Ω A)
    (K : MetricSourceProbe Ω) (t : ℝ)
    (inside : (originalEHPreparedAct s Ω A x).val+t•K ∈ wickOriginalMetricNeighborhood Ω)
    (q : RegisteredQuestion (KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) A)) :
    (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt
      (originalEHPreparedActCurve s Ω A x K t inside) (.inr q) =
    (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x (.inr q) := by
  induction x using Quotient.inductionOn with | _ x => cases q <;> rfl

theorem original_eh_prepared_actual_readout_derivative (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) (K : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ wickNativeFlatMetric
      ((originalEHPreparedAct s Ω A x).val+t•K))
      ((1/2:ℝ)*metricSourcePairing (originalEHPreparedEulerSource s Ω A κ Λ coupling x) K) 0 := by
  rw [original_eh_prepared_euler_half_pairing]
  exact original_eh_actual_act_hasDerivAt κ Λ coupling _ (originalEHPreparedAct s Ω A x).property K

theorem original_eh_prepared_curve_evaluation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) (K : MetricSourceProbe Ω) (t : ℝ)
    (inside : (originalEHPreparedAct s Ω A x).val+t•K ∈ wickOriginalMetricNeighborhood Ω) :
    (originalEHPreparedUse s Ω A κ Λ (originalEHPreparedActCurve s Ω A x K t inside)).2 =
      some (originalEHRelativeAction κ Λ wickNativeFlatMetric ((originalEHPreparedAct s Ω A x).val+t•K)) := by
  rw [original_eh_prepared_evaluation s Ω A κ Λ coupling,
    original_eh_prepared_curve_actual_operand]

end
end AASCKleinGordon
