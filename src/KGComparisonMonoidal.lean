import KGComparisonCoherence
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

theorem kg_family_right_unitor_naturality {a : Parameters} {A B : KGFamilyObject a}
    (f : A ⟶ B) :
    kgInternalTensor f (𝟙 (kgFamilyUnit a)) ≫ kgFamilyRightUnitor B=
      kgFamilyRightUnitor A ≫ f := by
  unfold kgFamilyRightUnitor
  rw [← Category.assoc,kg_family_symmetry_naturality,Category.assoc,
    kg_family_left_unitor_naturality,Category.assoc]

instance kgFamilyMonoidalStruct (a : Parameters) : MonoidalCategoryStruct (KGFamilyObject a) where
  tensorObj := kgFamilyTensor
  tensorHom := kgInternalTensor
  whiskerLeft A {_B _C} f := kgInternalTensor (𝟙 A) f
  whiskerRight {_A _B} f C := kgInternalTensor f (𝟙 C)
  tensorUnit := kgFamilyUnit a
  associator A B C := kgInternalIso (kgFamilyAssociator A B C)
  leftUnitor A := kgInternalIso (kgFamilyLeftUnitor A)
  rightUnitor A := kgInternalIso (kgFamilyRightUnitor A)

instance kgFamilyMonoidal (a : Parameters) : MonoidalCategory (KGFamilyObject a) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := kg_internal_tensor_identity)
    (id_tensorHom := fun _ {_B _C} _ => rfl)
    (tensorHom_id := fun {_A _B} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f g h k => (kg_internal_tensor_comp f h g k).symm)
    (associator_naturality := kg_family_associator_naturality)
    (leftUnitor_naturality := kg_family_left_unitor_naturality)
    (rightUnitor_naturality := kg_family_right_unitor_naturality)
    (pentagon := fun A B C D => (kg_family_pentagon A B C D).symm)
    (triangle := kg_family_triangle)

theorem kg_family_reverse_hexagon {a : Parameters} (A B C : KGFamilyObject a) :
    Groupoid.inv (kgFamilyAssociator A B C) ≫ kgFamilySymmetry (kgFamilyTensor A B) C ≫
        Groupoid.inv (kgFamilyAssociator C A B)=
      kgInternalTensor (𝟙 A) (kgFamilySymmetry B C) ≫
        Groupoid.inv (kgFamilyAssociator A C B) ≫
          kgInternalTensor (kgFamilySymmetry A C) (𝟙 B) := by
  apply kg_internal_arrow_ext
  have equality :
      (Groupoid.inv (kgFamilyAssociator A B C) ≫ kgFamilySymmetry (kgFamilyTensor A B) C ≫
        Groupoid.inv (kgFamilyAssociator C A B)).isometry.toLinearMap=
      (kgInternalTensor (𝟙 A) (kgFamilySymmetry B C) ≫
        Groupoid.inv (kgFamilyAssociator A C B) ≫
          kgInternalTensor (kgFamilySymmetry A C) (𝟙 B)).isometry.toLinearMap := by
    apply TensorProduct.ext'
    intro x yz
    induction yz using TensorProduct.induction_on with
    | zero => simp
    | tmul y z => rfl
    | add y z hy hz => simp only [TensorProduct.tmul_add,map_add,hy,hz]
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun equality)

instance kgFamilySymmetric (a : Parameters) : SymmetricCategory (KGFamilyObject a) where
  braiding A B := kgInternalIso (kgFamilySymmetry A B)
  braiding_naturality_right A {_B _C} f := kg_family_symmetry_naturality (𝟙 A) f
  braiding_naturality_left {_A _B} f B := kg_family_symmetry_naturality f (𝟙 B)
  hexagon_forward := kg_family_hexagon
  hexagon_reverse := kg_family_reverse_hexagon
  symmetry := kg_family_symmetry_involutive

end AASCKleinGordon
