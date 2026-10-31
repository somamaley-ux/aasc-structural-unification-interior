import KGQuantumOrbitDescent
import Mathlib.CategoryTheory.Groupoid

/-! The actual core-preserving comparison groupoid. Internal arrows intertwine
the declared diagonal Poincare continuation. Poincare changes of frame act
externally by conjugation, rather than being asserted to commute with boosts. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KGFamilyObject (a : Parameters) where
  shape : KGComparisonObject

abbrev KGFamilyCarrier {a : Parameters} (A : KGFamilyObject a) :=
  KGComparisonCarrier a A.shape

structure KGInternalArrow {a : Parameters} (A B : KGFamilyObject a) where
  isometry : KGFamilyCarrier A ≃ₗᵢ[ℂ] KGFamilyCarrier B
  intertwines : ∀ q x,
    isometry (kgComparisonPoincare a q A.shape x) =
      kgComparisonPoincare a q B.shape (isometry x)

@[ext] theorem kg_internal_arrow_ext {a : Parameters} {A B : KGFamilyObject a}
    {f g : KGInternalArrow A B} (h : f.isometry=g.isometry) : f=g := by
  cases f;cases g;cases h;rfl

def kgInternalIdentity {a : Parameters} (A : KGFamilyObject a) : KGInternalArrow A A :=
  ⟨LinearIsometryEquiv.refl ℂ _,fun _ _ => rfl⟩

def kgInternalCompose {a : Parameters} {A B C : KGFamilyObject a}
    (f : KGInternalArrow A B) (g : KGInternalArrow B C) : KGInternalArrow A C where
  isometry := f.isometry.trans g.isometry
  intertwines q x := by
    change g.isometry (f.isometry (kgComparisonPoincare a q A.shape x))=_
    rw [f.intertwines,g.intertwines]
    rfl

def kgInternalInverse {a : Parameters} {A B : KGFamilyObject a}
    (f : KGInternalArrow A B) : KGInternalArrow B A where
  isometry := f.isometry.symm
  intertwines q x := by
    apply f.isometry.injective
    rw [f.isometry.apply_symm_apply,f.intertwines,f.isometry.apply_symm_apply]

instance kgComparisonGroupoid (a : Parameters) : Groupoid (KGFamilyObject a) where
  Hom A B := KGInternalArrow A B
  id := kgInternalIdentity
  comp := kgInternalCompose
  id_comp f := by apply kg_internal_arrow_ext;ext x;rfl
  comp_id f := by apply kg_internal_arrow_ext;ext x;rfl
  assoc f g h := by apply kg_internal_arrow_ext;ext x;rfl
  inv := kgInternalInverse
  inv_comp f := by
    apply kg_internal_arrow_ext;ext x
    exact f.isometry.apply_symm_apply x
  comp_inv f := by
    apply kg_internal_arrow_ext;ext x
    exact f.isometry.symm_apply_apply x

def kgFamilyTensor {a : Parameters} (A B : KGFamilyObject a) : KGFamilyObject a :=
  ⟨.tensor A.shape B.shape⟩

def kgInternalTensor {a : Parameters} {A B C D : KGFamilyObject a}
    (f : A ⟶ B) (g : C ⟶ D) : kgFamilyTensor A C ⟶ kgFamilyTensor B D where
  isometry := TensorProduct.congrIsometry f.isometry g.isometry
  intertwines q x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change f.isometry (kgComparisonPoincare a q A.shape x) ⊗ₜ[ℂ]
          g.isometry (kgComparisonPoincare a q C.shape y) =
        kgComparisonPoincare a q B.shape (f.isometry x) ⊗ₜ[ℂ]
          kgComparisonPoincare a q D.shape (g.isometry y)
      rw [f.intertwines,g.intertwines]
    | add x y hx hy => simp only [map_add,hx,hy]

theorem kg_internal_tensor_identity {a : Parameters} (A B : KGFamilyObject a) :
    kgInternalTensor (𝟙 A) (𝟙 B)=𝟙 (kgFamilyTensor A B) := by
  apply kg_internal_arrow_ext
  have h : (kgInternalTensor (𝟙 A) (𝟙 B)).isometry.toLinearMap =
      (𝟙 (kgFamilyTensor A B) : kgFamilyTensor A B ⟶ kgFamilyTensor A B).isometry.toLinearMap := by
    apply TensorProduct.ext
    ext x y
    rfl
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun h)

theorem kg_internal_tensor_comp {a : Parameters} {A B C D E F : KGFamilyObject a}
    (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ E) (k : E ⟶ F) :
    kgInternalTensor (f ≫ g) (h ≫ k)=kgInternalTensor f h ≫ kgInternalTensor g k := by
  apply kg_internal_arrow_ext
  have equality : (kgInternalTensor (f ≫ g) (h ≫ k)).isometry.toLinearMap =
      (kgInternalTensor f h ≫ kgInternalTensor g k).isometry.toLinearMap := by
    apply TensorProduct.ext
    ext x y
    rfl
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun equality)

def kgFamilyTensorFunctor (a : Parameters) :
    KGFamilyObject a × KGFamilyObject a ⥤ KGFamilyObject a where
  obj X := kgFamilyTensor X.1 X.2
  map f := kgInternalTensor f.1 f.2
  map_id X := kg_internal_tensor_identity X.1 X.2
  map_comp f g := kg_internal_tensor_comp f.1 g.1 f.2 g.2

end AASCKleinGordon
