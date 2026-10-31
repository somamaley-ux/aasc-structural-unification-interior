import KGFamilyRecordLaws

/-! Evaluated questions, rather than free context syntax, carry the record
functor. Every original generated question is represented. Equality is equality
of its complete readout at every raw preparation, including failed execution. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def KGRealizedQuestion (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) :=
  {f : PureVector (KGFamilyCarrier A) → KGFamilyReadout //
    ∃ π : KGFamilyQuestion a Ω A,f=fun x => kgFamilyOutput a s Ω A x π}

def kgRealizeQuestion (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (π : KGFamilyQuestion a Ω A) : KGRealizedQuestion a s Ω A :=
  ⟨fun x => kgFamilyOutput a s Ω A x π,π,rfl⟩

def kgRealizedPullback (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGFamilyObject a} (f : A ⟶ B) (π : KGRealizedQuestion a s Ω B) :
    KGRealizedQuestion a s Ω A := by
  refine ⟨fun x => π.val (PureVector.mapUnitary f.isometry x),?_⟩
  obtain ⟨ρ,hρ⟩ := π.property
  refine ⟨kgFamilyQuestionPullback f ρ,?_⟩
  funext x
  rw [hρ]
  exact kg_family_arrow_output a s Ω f x ρ

theorem kg_realized_pullback_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (π : KGRealizedQuestion a s Ω A) :
    kgRealizedPullback a s Ω (𝟙 A) π=π := by
  apply Subtype.ext
  funext x
  rfl

theorem kg_realized_pullback_comp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B C : KGFamilyObject a} (f : A ⟶ B) (g : B ⟶ C)
    (π : KGRealizedQuestion a s Ω C) :
    kgRealizedPullback a s Ω (f ≫ g) π=
      kgRealizedPullback a s Ω f (kgRealizedPullback a s Ω g π) := by
  apply Subtype.ext
  funext x
  rfl

def kgRealizedRegion (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGFamilyObject a) (π : KGRealizedQuestion a s Ω A) :
    KGRealizedQuestion a s V A := by
  refine ⟨π.val,?_⟩
  obtain ⟨ρ,hρ⟩ := π.property
  refine ⟨kgFamilyQuestionExtend h ρ,?_⟩
  funext x
  rw [hρ]
  exact (kg_family_regional_output a s h A x ρ).symm

theorem kg_realized_region_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (π : KGRealizedQuestion a s Ω A) :
    kgRealizedRegion a s (le_refl Ω) A π=π := by apply Subtype.ext;rfl

theorem kg_realized_region_comp (a : Parameters) (s : ℝ) {Ω V W : Opens CoordinatePoint}
    (h : Ω ≤ V) (k : V ≤ W) (A : KGFamilyObject a) (π : KGRealizedQuestion a s Ω A) :
    kgRealizedRegion a s (le_trans h k) A π=
      kgRealizedRegion a s k A (kgRealizedRegion a s h A π) := by apply Subtype.ext;rfl

theorem kg_realized_region_arrow (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) {A B : KGFamilyObject a} (f : A ⟶ B) (π : KGRealizedQuestion a s Ω B) :
    kgRealizedRegion a s h A (kgRealizedPullback a s Ω f π)=
      kgRealizedPullback a s V f (kgRealizedRegion a s h B π) := by apply Subtype.ext;rfl

def kgRealizedFlow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (π : KGRealizedQuestion a s Ω A) :
    KGRealizedQuestion a s Ω A := by
  refine ⟨fun x => π.val (kgFamilyFlow q x),?_⟩
  obtain ⟨ρ,hρ⟩ := π.property
  refine ⟨kgFamilyFlowQuestion q ρ,?_⟩
  funext x
  rw [hρ]
  exact kg_family_flow_record a s Ω q A x ρ

theorem kg_realized_flow_arrow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) {A B : KGFamilyObject a} (f : A ⟶ B)
    (π : KGRealizedQuestion a s Ω B) :
    kgRealizedPullback a s Ω f (kgRealizedFlow a s Ω q B π)=
      kgRealizedFlow a s Ω q A (kgRealizedPullback a s Ω f π) := by
  apply Subtype.ext
  funext x
  exact congrArg π.val (kg_family_flow_internal_arrow q f x).symm

theorem kg_realized_flow_region (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (q : ProperPoincareTransform) (A : KGFamilyObject a)
    (π : KGRealizedQuestion a s Ω A) :
    kgRealizedRegion a s h A (kgRealizedFlow a s Ω q A π)=
      kgRealizedFlow a s V q A (kgRealizedRegion a s h A π) := by apply Subtype.ext;rfl

end AASCKleinGordon
