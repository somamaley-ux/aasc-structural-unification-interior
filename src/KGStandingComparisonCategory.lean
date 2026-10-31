import RegisteredStandingReferences
import KGComparisonMonoidal

/-! A comparison category with constructed quotient-state arrows. The tensor
object contains all algebraic tensor states; it is not a Cartesian product of
ray spaces. The closing functor is strong symmetric monoidal at these objects. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KGStandingObject (a : Parameters) where
  raw : KGFamilyObject a

structure KGStandingArrow {a : Parameters} (A B : KGStandingObject a) where
  rawArrow : A.raw ⟶ B.raw
  stateMap : PhysicalRay (KGFamilyCarrier A.raw) → PhysicalRay (KGFamilyCarrier B.raw)
  source_square : ∀ x,stateMap (rayMap _ x)=rayMap _ (PureVector.mapUnitary rawArrow.isometry x)

def kgCloseArrow {a : Parameters} {A B : KGStandingObject a} (f : A.raw ⟶ B.raw) :
    KGStandingArrow A B := ⟨f,unitaryRayMap f.isometry,fun _ => rfl⟩

@[ext] theorem kg_standing_arrow_ext {a : Parameters} {A B : KGStandingObject a}
    {f g : KGStandingArrow A B} (h : f.rawArrow=g.rawArrow) : f=g := by
  have states : f.stateMap=g.stateMap := by
    funext r
    induction r using Quotient.inductionOn with
    | _ x =>
      change f.stateMap (rayMap _ x)=g.stateMap (rayMap _ x)
      rw [f.source_square,g.source_square,h]
  cases f;cases g;cases h;cases states;rfl

def kgStandingCompose {a : Parameters} {A B C : KGStandingObject a}
    (f : KGStandingArrow A B) (g : KGStandingArrow B C) : KGStandingArrow A C where
  rawArrow := f.rawArrow ≫ g.rawArrow
  stateMap r := g.stateMap (f.stateMap r)
  source_square x := by
    rw [f.source_square,g.source_square]
    rfl

instance kgStandingGroupoid (a : Parameters) : Groupoid (KGStandingObject a) where
  Hom := KGStandingArrow
  id A := kgCloseArrow (𝟙 A.raw)
  comp := kgStandingCompose
  id_comp f := by apply kg_standing_arrow_ext;exact Category.id_comp f.rawArrow
  comp_id f := by apply kg_standing_arrow_ext;exact Category.comp_id f.rawArrow
  assoc f g h := by apply kg_standing_arrow_ext;exact Category.assoc f.rawArrow g.rawArrow h.rawArrow
  inv f := kgCloseArrow (Groupoid.inv f.rawArrow)
  inv_comp f := by apply kg_standing_arrow_ext;exact Groupoid.inv_comp f.rawArrow
  comp_inv f := by apply kg_standing_arrow_ext;exact Groupoid.comp_inv f.rawArrow

def kgStandingIso {a : Parameters} {A B : KGStandingObject a} (f : A ⟶ B) : A ≅ B :=
  ⟨f,Groupoid.inv f,Groupoid.comp_inv f,Groupoid.inv_comp f⟩

def kgStandingTensor {a : Parameters} (A B : KGStandingObject a) : KGStandingObject a :=
  ⟨kgFamilyTensor A.raw B.raw⟩

def kgStandingTensorArrow {a : Parameters} {A B C D : KGStandingObject a}
    (f : A ⟶ B) (g : C ⟶ D) : kgStandingTensor A C ⟶ kgStandingTensor B D :=
  kgCloseArrow (kgInternalTensor f.rawArrow g.rawArrow)

instance kgStandingMonoidalStruct (a : Parameters) : MonoidalCategoryStruct (KGStandingObject a) where
  tensorObj := kgStandingTensor
  tensorHom := kgStandingTensorArrow
  whiskerLeft A {_B _C} f := kgStandingTensorArrow (𝟙 A) f
  whiskerRight {_A _B} f C := kgStandingTensorArrow f (𝟙 C)
  tensorUnit := ⟨kgFamilyUnit a⟩
  associator A B C := kgStandingIso (kgCloseArrow (kgFamilyAssociator A.raw B.raw C.raw))
  leftUnitor A := kgStandingIso (kgCloseArrow (kgFamilyLeftUnitor A.raw))
  rightUnitor A := kgStandingIso (kgCloseArrow (kgFamilyRightUnitor A.raw))

instance kgStandingMonoidal (a : Parameters) : MonoidalCategory (KGStandingObject a) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun A B => by
      apply kg_standing_arrow_ext;exact kg_internal_tensor_identity A.raw B.raw)
    (id_tensorHom := fun _ {_B _C} _ => rfl)
    (tensorHom_id := fun {_A _B} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f g h k => by
      apply kg_standing_arrow_ext;exact (kg_internal_tensor_comp f.rawArrow h.rawArrow g.rawArrow k.rawArrow).symm)
    (associator_naturality := fun f g h => by
      apply kg_standing_arrow_ext;exact kg_family_associator_naturality f.rawArrow g.rawArrow h.rawArrow)
    (leftUnitor_naturality := fun f => by
      apply kg_standing_arrow_ext;exact kg_family_left_unitor_naturality f.rawArrow)
    (rightUnitor_naturality := fun f => by
      apply kg_standing_arrow_ext;exact kg_family_right_unitor_naturality f.rawArrow)
    (pentagon := fun A B C D => by
      apply kg_standing_arrow_ext;exact (kg_family_pentagon A.raw B.raw C.raw D.raw).symm)
    (triangle := fun A B => by
      apply kg_standing_arrow_ext;exact kg_family_triangle A.raw B.raw)

instance kgStandingSymmetric (a : Parameters) : SymmetricCategory (KGStandingObject a) where
  braiding A B := kgStandingIso (kgCloseArrow (kgFamilySymmetry A.raw B.raw))
  braiding_naturality_right A {_B _C} f := by
    apply kg_standing_arrow_ext;exact kg_family_symmetry_naturality (𝟙 A.raw) f.rawArrow
  braiding_naturality_left {_A _B} f B := by
    apply kg_standing_arrow_ext;exact kg_family_symmetry_naturality f.rawArrow (𝟙 B.raw)
  hexagon_forward A B C := by
    apply kg_standing_arrow_ext;exact kg_family_hexagon A.raw B.raw C.raw
  hexagon_reverse A B C := by
    apply kg_standing_arrow_ext;exact kg_family_reverse_hexagon A.raw B.raw C.raw
  symmetry A B := by
    apply kg_standing_arrow_ext;exact kg_family_symmetry_involutive A.raw B.raw

def kgQCloseComparison (a : Parameters) : KGFamilyObject a ⥤ KGStandingObject a where
  obj A := ⟨A⟩
  map f := kgCloseArrow f
  map_id _ := rfl
  map_comp _ _ := by apply kg_standing_arrow_ext;rfl

open scoped MonoidalCategory

def kgQCloseCoreMonoidal (a : Parameters) : (kgQCloseComparison a).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f A := by
    apply kg_standing_arrow_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  μIso_hom_natural_right A f := by
    apply kg_standing_arrow_ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  associativity A B C := by
    apply kg_standing_arrow_ext
    change kgInternalTensor (𝟙 (kgFamilyTensor A B)) (𝟙 C) ≫ 𝟙 _ ≫ kgFamilyAssociator A B C =
      kgFamilyAssociator A B C ≫ kgInternalTensor (𝟙 A) (𝟙 (kgFamilyTensor B C)) ≫ 𝟙 _
    rw [kg_internal_tensor_identity,kg_internal_tensor_identity]
    simp only [Category.id_comp,Category.comp_id]
  left_unitality A := by
    apply kg_standing_arrow_ext
    change kgFamilyLeftUnitor A=kgInternalTensor (𝟙 (kgFamilyUnit a)) (𝟙 A) ≫ 𝟙 _ ≫ kgFamilyLeftUnitor A
    rw [kg_internal_tensor_identity]
    simp only [Category.id_comp]
  right_unitality A := by
    apply kg_standing_arrow_ext
    change kgFamilyRightUnitor A=kgInternalTensor (𝟙 A) (𝟙 (kgFamilyUnit a)) ≫ 𝟙 _ ≫ kgFamilyRightUnitor A
    rw [kg_internal_tensor_identity]
    simp only [Category.id_comp]

instance kgQCloseMonoidal (a : Parameters) : (kgQCloseComparison a).Monoidal :=
  (kgQCloseCoreMonoidal a).toMonoidal

instance kgQCloseBraided (a : Parameters) : (kgQCloseComparison a).LaxBraided where
  braided A B := by
    apply kg_standing_arrow_ext
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end AASCKleinGordon
