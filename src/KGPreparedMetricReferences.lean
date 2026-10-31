import KGPreparedMetricUse

/-! The complete reference profile of an actual prepared metric use. The field
entries and registered preparation references are compared before descending.
This is the declared finite-act profile, not an Einstein evolution law. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

abbrev KGPreparedQuestion {a : Parameters} (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :=
  (Spacetime × Fin 4 × Fin 4) ⊕ RegisteredQuestion (KGChartFamilyQuestion a Ω D A)

abbrev KGPreparedReadout := ℝ ⊕ KGFamilyReadout

def kgPreparedRawReference {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : KGPreparedMetricRaw Ω D A) :
    KGPreparedQuestion Ω D A → Option KGPreparedReadout := by
  classical
  exact fun
  | .inl (p,i,j) => some (.inl (wickOriginalFiniteMetric x.act.val p i j))
  | .inr (.execution π) => if kgFamilySuccess (kgChartFamilyOutput a s Ω D A x.preparation π)
      then some (.inr (kgChartFamilyOutput a s Ω D A x.preparation π)) else none
  | .inr (.ledger π) => some (.inr (kgChartFamilyOutput a s Ω D A x.preparation π))

theorem kg_prepared_raw_references_exact {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x y : KGPreparedMetricRaw Ω D A) :
    (∀ π,kgPreparedRawReference s Ω D A x π=kgPreparedRawReference s Ω D A y π) ↔
      kgPreparedMetricSame s Ω D A x y := by
  classical
  constructor
  · intro h
    constructor
    · funext p i j
      exact Sum.inl.inj (Option.some.inj (h (.inl (p,i,j))))
    · intro π
      exact Sum.inr.inj (Option.some.inj (h (.inr (.ledger π))))
  · rintro ⟨metric,record⟩ π
    cases π with
    | inl point => simp only [kgPreparedRawReference,metric]
    | inr π =>
      cases π with
      | execution π => simp only [kgPreparedRawReference,record π]
      | ledger π => simp only [kgPreparedRawReference,record π]

def kgPreparedReferences {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    AASC.PartialReferenceSystem (KGPreparedMetricUse s Ω D A) (KGPreparedQuestion Ω D A) KGPreparedReadout :=
  ⟨Quotient.lift (kgPreparedRawReference s Ω D A) (fun x y h =>
    funext ((kg_prepared_raw_references_exact s Ω D A x y).mpr h))⟩

theorem kg_prepared_reference_raw_square {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : KGPreparedMetricRaw Ω D A)
    (π : KGPreparedQuestion Ω D A) :
    (kgPreparedReferences s Ω D A).referenceAt (Quotient.mk _ x) π=
      kgPreparedRawReference s Ω D A x π := rfl

theorem kg_prepared_reference_profile_faithful {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x y : KGPreparedMetricUse s Ω D A)
    (same : ∀ π,(kgPreparedReferences s Ω D A).referenceAt x π=
      (kgPreparedReferences s Ω D A).referenceAt y π) : x=y := by
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      exact Quotient.sound ((kg_prepared_raw_references_exact s Ω D A x y).mp same)

theorem kg_prepared_registered_original_square {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : KGPreparedMetricRaw Ω D A)
    (π : RegisteredQuestion (KGChartFamilyQuestion a Ω D A)) :
    kgPreparedRawReference s Ω D A x (.inr π)=
      ((kgChartRawRegisteredOrbit a s Ω D A).references.referenceAt x.preparation π).map Sum.inr := by
  classical
  cases π with
  | execution π =>
    change (if kgFamilySuccess (kgChartFamilyOutput a s Ω D A x.preparation π)
      then some (.inr (kgChartFamilyOutput a s Ω D A x.preparation π)) else none)=
      (if kgFamilySuccess (kgChartFamilyOutput a s Ω D A x.preparation π)
      then some (kgChartFamilyOutput a s Ω D A x.preparation π) else none).map Sum.inr
    split <;> rfl
  | ledger π => rfl

theorem kg_prepared_registered_standing_square {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : KGPreparedMetricUse s Ω D A)
    (π : RegisteredQuestion (KGChartFamilyQuestion a Ω D A)) :
    (kgPreparedReferences s Ω D A).referenceAt x (.inr π)=
      ((kgChartRawRegisteredOrbit a s Ω D A).standingReferences.referenceAt
        (kgPreparedQuantum s Ω D A x) π).map Sum.inr := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change kgPreparedRawReference s Ω D A x (.inr π)=
      ((kgChartRawRegisteredOrbit a s Ω D A).standingReferences.referenceAt
        (rayMap _ x.preparation) π).map Sum.inr
    exact (kg_prepared_registered_original_square s Ω D A x π).trans
      (congrArg (Option.map Sum.inr)
        ((kgChartRawRegisteredOrbit a s Ω D A).standing_reference_square x.preparation π)).symm

theorem kg_prepared_references_determinate {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    (kgPreparedReferences s Ω D A).incidenceSystem.Determinate :=
  (kgPreparedReferences s Ω D A).determinate

end AASCKleinGordon
