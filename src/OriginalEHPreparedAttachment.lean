import OriginalEHMetricActGeometry
import KGPreparedOriginalSource
import OriginalEHGeometricCore

/-! A concrete readout on the already constructed original prepared-use
carrier. The operand is extracted from that carrier; no arbitrary operand
function or desired correspondence field is an input. The original references
and source attachment remain the existing ones. This bounded metric-act
attachment is not an assertion of the entire original gravity/AER interface. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace

variable {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint) (A : KGFamilyObject a)

abbrev OriginalEHPreparedUse :=
  KGPreparedMetricUse s Ω (wickOriginalMetricNeighborhood Ω) A

def originalEHPreparedAct (x : OriginalEHPreparedUse s Ω A) :=
  kgPreparedMetricAct s Ω (wickOriginalMetricNeighborhood Ω) A x

def originalEHPreparedMetric (x : OriginalEHPreparedUse s Ω A) : MetricField :=
  originalEHActMetric (originalEHPreparedAct s Ω A x).val

def originalEHPreparedUse (κ Λ : ℝ) (x : OriginalEHPreparedUse s Ω A) :=
  originalEHFiniteUse κ Λ wickNativeFlatMetric (originalEHPreparedAct s Ω A x).val

theorem original_eh_prepared_raw_operand
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) A) :
    originalEHPreparedAct s Ω A (Quotient.mk _ x) = x.act := rfl

theorem original_eh_prepared_raw_action (κ Λ : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) A) :
    originalEHPreparedUse s Ω A κ Λ (Quotient.mk _ x) =
      originalEHFiniteUse κ Λ wickNativeFlatMetric x.act.val := rfl

theorem original_eh_prepared_same_metric_field (x : OriginalEHPreparedUse s Ω A)
    (p : Spacetime) :
    originalEHPreparedMetric s Ω A x (wickSpacetimeCoordinates p) =
      kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) A x p := by
  rw [kg_prepared_metric_field_eq]
  rfl

theorem original_eh_raw_action_respects_original_profiles (κ Λ : ℝ)
    (x y : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) A)
    (same : kgPreparedMetricSame s Ω (wickOriginalMetricNeighborhood Ω) A x y) :
    originalEHFiniteUse κ Λ wickNativeFlatMetric x.act.val =
      originalEHFiniteUse κ Λ wickNativeFlatMetric y.act.val := by
  have acts := ((kg_prepared_metric_same_iff s Ω (wickOriginalMetricNeighborhood Ω) A x y).mp same).1
  exact congrArg (fun H => originalEHFiniteUse κ Λ wickNativeFlatMetric H.val) acts

theorem original_eh_prepared_admitted (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) :
    OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric (originalEHPreparedAct s Ω A x).val :=
  original_eh_original_act_admitted κ Λ coupling _ (originalEHPreparedAct s Ω A x).property

theorem original_eh_prepared_evaluation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) :
    (originalEHPreparedUse s Ω A κ Λ x).2 = some
      (originalEHRelativeAction κ Λ wickNativeFlatMetric (originalEHPreparedAct s Ω A x).val) :=
  original_eh_original_act_evaluation κ Λ coupling _ (originalEHPreparedAct s Ω A x).property

def originalEHPreparedReferences (κ Λ : ℝ) :
    AASC.PartialReferenceSystem (OriginalEHPreparedUse s Ω A)
      (KGPreparedQuestion Ω (wickOriginalMetricNeighborhood Ω) A ⊕ Unit)
      (KGPreparedReadout ⊕ ℝ) where
  referenceAt x q := match q with
    | .inl old => ((kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x old).map Sum.inl
    | .inr _ => (originalEHPreparedUse s Ω A κ Λ x).2.map Sum.inr

theorem original_eh_prepared_old_reference_square (κ Λ : ℝ)
    (x : OriginalEHPreparedUse s Ω A)
    (q : KGPreparedQuestion Ω (wickOriginalMetricNeighborhood Ω) A) :
    (originalEHPreparedReferences s Ω A κ Λ).referenceAt x (.inl q) =
      ((kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q).map Sum.inl := rfl

theorem original_eh_prepared_old_failure_exact (κ Λ : ℝ)
    (x : OriginalEHPreparedUse s Ω A)
    (q : KGPreparedQuestion Ω (wickOriginalMetricNeighborhood Ω) A) :
    (originalEHPreparedReferences s Ω A κ Λ).referenceAt x (.inl q) = none ↔
      (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q = none := by
  rw [original_eh_prepared_old_reference_square]
  cases (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q <;> simp

theorem original_eh_prepared_old_standing_exact (κ Λ : ℝ)
    (x : OriginalEHPreparedUse s Ω A)
    (q : KGPreparedQuestion Ω (wickOriginalMetricNeighborhood Ω) A) :
    (originalEHPreparedReferences s Ω A κ Λ).incidenceSystem.AdmissibleAt x (.inl q) ↔
      (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).incidenceSystem.AdmissibleAt x q := by
  change (∃ v, Option.map Sum.inl
    ((kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q) = some v) ↔
      ∃ v, (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q = some v
  cases (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q <;> simp

theorem original_eh_prepared_reference_profile_faithful (κ Λ : ℝ)
    (x y : OriginalEHPreparedUse s Ω A)
    (same : ∀ q, (originalEHPreparedReferences s Ω A κ Λ).referenceAt x q =
      (originalEHPreparedReferences s Ω A κ Λ).referenceAt y q) : x = y := by
  apply kg_prepared_reference_profile_faithful s Ω (wickOriginalMetricNeighborhood Ω) A x y
  intro q
  have h := same (.inl q)
  rw [original_eh_prepared_old_reference_square,original_eh_prepared_old_reference_square] at h
  cases hx : (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x q <;>
    cases hy : (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt y q <;>
      simp_all

def originalEHPreparedFirstVariation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  originalEHFirstVariation κ Λ coupling (originalEHPreparedMetric s Ω A x)
    (original_eh_act_metric_symmetric _) (original_eh_act_metric_smooth _)
    (fun p _ => original_eh_act_metric_negative _ (originalEHPreparedAct s Ω A x).property p)

def originalEHPreparedEulerSource (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) : SymmetricSourceComponents Ω :=
  representedMetricSource (originalEHPreparedFirstVariation s Ω A κ Λ coupling x)

theorem original_eh_prepared_first_variation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) :
    EHOriginalFirstVariationProperty κ Λ (originalEHPreparedMetric s Ω A x)
      (originalEHPreparedFirstVariation s Ω A κ Λ coupling x) :=
  eh_original_first_variation_hasDerivAt κ Λ coupling _ _ _ _

theorem original_eh_prepared_euler_half_pairing (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) (K : MetricSourceProbe Ω) :
    (1/2:ℝ) * metricSourcePairing (originalEHPreparedEulerSource s Ω A κ Λ coupling x) K =
      originalEHPreparedFirstVariation s Ω A κ Λ coupling x K :=
  constructed_metric_source_represents _ K

theorem original_eh_prepared_euler_same_metric_density (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : OriginalEHPreparedUse s Ω A) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    originalEHPreparedEulerSource s Ω A κ Λ coupling x i φ =
      ∫ p, sourceDensityCoordinates
        (raisedSourceTensorDensity (originalEHPreparedMetric s Ω A x)
          (originalEHGeometricResponse κ Λ (originalEHPreparedMetric s Ω A x))) i p * φ p :=
  eh_original_geometric_tensor_represents_action_source κ Λ coupling _ _ _ _ i φ

end
end AASCKleinGordon
