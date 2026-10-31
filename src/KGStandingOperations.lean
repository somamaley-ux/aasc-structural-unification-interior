import KGStandingComparisonCategory
import KGRealizedQuestions
import KGFamilyStandingDescent

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

namespace W9

def mapRegisteredQuestion {Q R : Type} (f : Q → R) : RegisteredQuestion Q → RegisteredQuestion R
  | .execution π => .execution (f π)
  | .ledger π => .ledger (f π)

theorem reference_from_record_square {X Q V P Y R S : Type}
    (D : RawRegisteredOrbit X Q V P) (E : RawRegisteredOrbit Y R V S)
    (x : X) (y : Y) (f : Q → R) (success : E.succeeds=D.succeeds)
    (output : ∀ π,E.output y (f π)=D.output x π) (π : RegisteredQuestion Q) :
    E.references.referenceAt y (mapRegisteredQuestion f π)=D.references.referenceAt x π := by
  classical
  cases π with
  | execution π =>
    change (if E.succeeds (E.output y (f π)) then some (E.output y (f π)) else none)=
      (if D.succeeds (D.output x π) then some (D.output x π) else none)
    rw [output,success]
  | ledger π => exact congrArg some (output π)

end W9

theorem kg_raw_arrow_reference (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGFamilyObject a} (f : A ⟶ B) (x : PureVector (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω B)) :
    (kgRawRegisteredOrbit a s Ω A).references.referenceAt x
      (mapRegisteredQuestion (kgFamilyQuestionPullback f) π)=
    (kgRawRegisteredOrbit a s Ω B).references.referenceAt (PureVector.mapUnitary f.isometry x) π :=
  reference_from_record_square (kgRawRegisteredOrbit a s Ω B)
    (kgRawRegisteredOrbit a s Ω A) (PureVector.mapUnitary f.isometry x) x
    (kgFamilyQuestionPullback f) rfl (fun π => (kg_family_arrow_output a s Ω f x π).symm) π

theorem kg_raw_region_reference (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω A)) :
    (kgRawRegisteredOrbit a s V A).references.referenceAt x
      (mapRegisteredQuestion (kgFamilyQuestionExtend h) π)=
      (kgRawRegisteredOrbit a s Ω A).references.referenceAt x π :=
  reference_from_record_square (kgRawRegisteredOrbit a s Ω A)
    (kgRawRegisteredOrbit a s V A) x x (kgFamilyQuestionExtend h)
    rfl (kg_family_regional_output a s h A x) π

theorem kg_raw_flow_reference (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω A)) :
    (kgRawRegisteredOrbit a s Ω A).references.referenceAt x
      (mapRegisteredQuestion (kgFamilyFlowQuestion q) π)=
      (kgRawRegisteredOrbit a s Ω A).references.referenceAt (kgFamilyFlow q x) π :=
  reference_from_record_square (kgRawRegisteredOrbit a s Ω A)
    (kgRawRegisteredOrbit a s Ω A) (kgFamilyFlow q x) x (kgFamilyFlowQuestion q)
    rfl (fun π => (kg_family_flow_record a s Ω q A x π).symm) π

section ContinuousArrows
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem kg_pure_unitary_continuous (U : E ≃ₗᵢ[ℂ] F) : Continuous (PureVector.mapUnitary U) :=
  (U.continuous.comp continuous_subtype_val).subtype_mk _

theorem kg_ray_unitary_continuous (U : E ≃ₗᵢ[ℂ] F) : Continuous (unitaryRayMap U) := by
  unfold unitaryRayMap
  exact ((kg_raw_orbit_map_continuous (E := F)).comp (kg_pure_unitary_continuous U)).quotient_lift _

end ContinuousArrows

theorem kg_standing_arrow_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGStandingObject a} (f : A ⟶ B) (r : PhysicalRay (KGFamilyCarrier A.raw))
    (π : KGFamilyQuestion a Ω B.raw) :
    kgW9StandingRecord a s Ω B.raw (f.stateMap r) π=
      kgW9StandingRecord a s Ω A.raw r (kgFamilyQuestionPullback f.rawArrow π) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgW9StandingRecord a s Ω B.raw (f.stateMap (rayMap _ x)) π=
      kgW9StandingRecord a s Ω A.raw (rayMap _ x) _
    rw [f.source_square,kg_w9_standing_complete_record,kg_w9_standing_complete_record]
    exact kg_family_arrow_output a s Ω f.rawArrow x π

theorem kg_standing_region_record (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω A) :
    kgW9StandingRecord a s V A r (kgFamilyQuestionExtend h π)=kgW9StandingRecord a s Ω A r π := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgW9StandingRecord a s V A (rayMap _ x) _=kgW9StandingRecord a s Ω A (rayMap _ x) π
    rw [kg_w9_standing_complete_record,kg_w9_standing_complete_record]
    exact kg_family_regional_output a s h A x π

theorem kg_standing_arrow_reference (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGStandingObject a} (f : A ⟶ B) (r : PhysicalRay (KGFamilyCarrier A.raw))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω B.raw)) :
    (kgRawRegisteredOrbit a s Ω B.raw).standingReferences.referenceAt (f.stateMap r) π=
      (kgRawRegisteredOrbit a s Ω A.raw).standingReferences.referenceAt r
        (mapRegisteredQuestion (kgFamilyQuestionPullback f.rawArrow) π) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change (kgRawRegisteredOrbit a s Ω B.raw).standingReferences.referenceAt (f.stateMap (rayMap _ x)) π=_
    rw [f.source_square]
    exact ((kgRawRegisteredOrbit a s Ω B.raw).standing_reference_square
      (PureVector.mapUnitary f.rawArrow.isometry x) π).trans
      ((kg_raw_arrow_reference a s Ω f.rawArrow x π).symm.trans
        ((kgRawRegisteredOrbit a s Ω A.raw).standing_reference_square x
          (mapRegisteredQuestion (kgFamilyQuestionPullback f.rawArrow) π)).symm)

theorem kg_standing_region_reference (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω A)) :
    (kgRawRegisteredOrbit a s V A).standingReferences.referenceAt r
      (mapRegisteredQuestion (kgFamilyQuestionExtend h) π)=
      (kgRawRegisteredOrbit a s Ω A).standingReferences.referenceAt r π := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change (kgRawRegisteredOrbit a s V A).standingReferences.referenceAt (rayMap _ x) _=
      (kgRawRegisteredOrbit a s Ω A).standingReferences.referenceAt (rayMap _ x) π
    exact ((kgRawRegisteredOrbit a s V A).standing_reference_square x
      (mapRegisteredQuestion (kgFamilyQuestionExtend h) π)).trans
      ((kg_raw_region_reference a s h A x π).trans
        ((kgRawRegisteredOrbit a s Ω A).standing_reference_square x π).symm)

def kgStandingFlow {a : Parameters} (q : ProperPoincareTransform) (A : KGFamilyObject a) :
    PhysicalRay (KGFamilyCarrier A) → PhysicalRay (KGFamilyCarrier A) :=
  unitaryRayMap (kgComparisonPoincare a q A.shape)

theorem kg_standing_flow_unique (a : Parameters) (q : ProperPoincareTransform)
    (A : KGFamilyObject a) : ∃! C : PhysicalRay (KGFamilyCarrier A) → PhysicalRay (KGFamilyCarrier A),
      ∀ x,C (rayMap _ x)=rayMap _ (kgFamilyFlow q x) :=
  kg_descended_continuation_unique (kgComparisonPoincare a q A.shape)

theorem kg_standing_flow_continuous (a : Parameters) (q : ProperPoincareTransform)
    (A : KGFamilyObject a) : Continuous (kgStandingFlow q A) :=
  kg_ray_unitary_continuous (kgComparisonPoincare a q A.shape)

theorem kg_standing_flow_probability (a : Parameters) (q : ProperPoincareTransform)
    (A : KGFamilyObject a) (r t : PhysicalRay (KGFamilyCarrier A)) :
    rayTransitionProbability (kgStandingFlow q A r) (kgStandingFlow q A t)=rayTransitionProbability r t :=
  rayTransitionProbability_unitary_invariant (kgComparisonPoincare a q A.shape) r t

theorem kg_standing_flow_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω A) :
    kgW9StandingRecord a s Ω A (kgStandingFlow q A r) π=
      kgW9StandingRecord a s Ω A r (kgFamilyFlowQuestion q π) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgW9StandingRecord a s Ω A (rayMap _ (kgFamilyFlow q x)) π=
      kgW9StandingRecord a s Ω A (rayMap _ x) _
    rw [kg_w9_standing_complete_record,kg_w9_standing_complete_record]
    exact kg_family_flow_record a s Ω q A x π

def kgStandingFirstFailure (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A)) :=
  kgFirstFailure (kgW9StandingRecord a s Ω A r)

theorem kg_standing_first_failure_spec (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) (word : List (KGFamilyQuestion a Ω A)) :
    kgStandingFirstFailure a s Ω A (rayMap _ x) word=kgFirstFailure (kgFamilyOutput a s Ω A x) word := by
  have eq : kgW9StandingRecord a s Ω A (rayMap _ x)=kgFamilyOutput a s Ω A x :=
    funext (kg_w9_standing_complete_record a s Ω A x)
  exact congrArg (fun output => kgFirstFailure output word) eq

theorem kg_standing_first_failure_arrow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGStandingObject a} (f : A ⟶ B) (r : PhysicalRay (KGFamilyCarrier A.raw))
    (word : List (KGFamilyQuestion a Ω B.raw)) :
    kgStandingFirstFailure a s Ω A.raw r (word.map (kgFamilyQuestionPullback f.rawArrow))=
      kgStandingFirstFailure a s Ω B.raw (f.stateMap r) word :=
  kg_first_failure_map _ _ _ (fun π => (kg_standing_arrow_record a s Ω f r π).symm) word

theorem kg_standing_first_failure_region (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGFamilyObject a)
    (r : PhysicalRay (KGFamilyCarrier A)) (word : List (KGFamilyQuestion a Ω A)) :
    kgStandingFirstFailure a s V A r (word.map (kgFamilyQuestionExtend h))=
      kgStandingFirstFailure a s Ω A r word :=
  kg_first_failure_map _ _ _ (kg_standing_region_record a s h A r) word

theorem kg_standing_first_failure_flow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A))
    (word : List (KGFamilyQuestion a Ω A)) :
    kgStandingFirstFailure a s Ω A r (word.map (kgFamilyFlowQuestion q))=
      kgStandingFirstFailure a s Ω A (kgStandingFlow q A r) word :=
  kg_first_failure_map _ _ _ (fun π => (kg_standing_flow_record a s Ω q A r π).symm) word

theorem kg_standing_flow_tensor (a : Parameters) (q : ProperPoincareTransform)
    (A B : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A)) (t : PhysicalRay (KGFamilyCarrier B)) :
    kgStandingFlow q (kgFamilyTensor A B) (kgTensorRay r t)=
      kgTensorRay (kgStandingFlow q A r) (kgStandingFlow q B t) :=
  kg_tensor_ray_continuation a q A.shape B.shape r t

theorem kg_standing_tensor_arrow_natural (a : Parameters) {A B C D : KGStandingObject a}
    (f : A ⟶ B) (g : C ⟶ D) (r : PhysicalRay (KGFamilyCarrier A.raw))
    (t : PhysicalRay (KGFamilyCarrier C.raw)) :
    (kgStandingTensorArrow f g).stateMap (kgTensorRay r t)=kgTensorRay (f.stateMap r) (g.stateMap t) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    induction t using Quotient.inductionOn with
    | _ y =>
      change (kgStandingTensorArrow f g).stateMap (kgTensorRay (rayMap _ x) (rayMap _ y))=
        kgTensorRay (f.stateMap (rayMap _ x)) (g.stateMap (rayMap _ y))
      rw [f.source_square,g.source_square]
      rfl

end AASCKleinGordon
