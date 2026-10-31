import KGComparisonGroupoid

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgFamilyUnit (a : Parameters) : KGFamilyObject a := ⟨.unit⟩

def kgFamilyAssociator {a : Parameters} (A B C : KGFamilyObject a) :
    kgFamilyTensor (kgFamilyTensor A B) C ⟶ kgFamilyTensor A (kgFamilyTensor B C) where
  isometry := TensorProduct.assocIsometry ℂ (KGFamilyCarrier A) (KGFamilyCarrier B) (KGFamilyCarrier C)
  intertwines q z := by
    have equality :
        (TensorProduct.assocIsometry ℂ (KGFamilyCarrier A) (KGFamilyCarrier B)
          (KGFamilyCarrier C)).toLinearMap.comp
            (kgComparisonPoincare a q (.tensor (.tensor A.shape B.shape) C.shape)).toLinearMap =
        (kgComparisonPoincare a q (.tensor A.shape (.tensor B.shape C.shape))).toLinearMap.comp
          (TensorProduct.assocIsometry ℂ (KGFamilyCarrier A) (KGFamilyCarrier B)
            (KGFamilyCarrier C)).toLinearMap := by
      apply TensorProduct.ext_threefold
      intro x y z
      rfl
    exact LinearMap.congr_fun equality z

def kgFamilyLeftUnitor {a : Parameters} (A : KGFamilyObject a) :
    kgFamilyTensor (kgFamilyUnit a) A ⟶ A where
  isometry := TensorProduct.lidIsometry ℂ (KGFamilyCarrier A)
  intertwines q z := by
    have equality : (TensorProduct.lidIsometry ℂ (KGFamilyCarrier A)).toLinearMap.comp
        (kgComparisonPoincare a q (.tensor .unit A.shape)).toLinearMap =
        (kgComparisonPoincare a q A.shape).toLinearMap.comp
          (TensorProduct.lidIsometry ℂ (KGFamilyCarrier A)).toLinearMap := by
      apply TensorProduct.ext'
      intro c x
      change ℂ at c
      change (c : ℂ) • kgComparisonPoincare a q A.shape x=kgComparisonPoincare a q A.shape ((c : ℂ) • x)
      exact ((kgComparisonPoincare a q A.shape).map_smul (c : ℂ) x).symm
    exact LinearMap.congr_fun equality z

def kgFamilySymmetry {a : Parameters} (A B : KGFamilyObject a) :
    kgFamilyTensor A B ⟶ kgFamilyTensor B A where
  isometry := TensorProduct.commIsometry ℂ (KGFamilyCarrier A) (KGFamilyCarrier B)
  intertwines q z := by
    have equality :
        (TensorProduct.commIsometry ℂ (KGFamilyCarrier A) (KGFamilyCarrier B)).toLinearMap.comp
          (kgComparisonPoincare a q (.tensor A.shape B.shape)).toLinearMap =
        (kgComparisonPoincare a q (.tensor B.shape A.shape)).toLinearMap.comp
          (TensorProduct.commIsometry ℂ (KGFamilyCarrier A) (KGFamilyCarrier B)).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    exact LinearMap.congr_fun equality z

def kgFamilyRightUnitor {a : Parameters} (A : KGFamilyObject a) :
    kgFamilyTensor A (kgFamilyUnit a) ⟶ A :=
  kgFamilySymmetry A (kgFamilyUnit a) ≫ kgFamilyLeftUnitor A

def kgInternalIso {a : Parameters} {A B : KGFamilyObject a} (f : A ⟶ B) : A ≅ B :=
  ⟨f,Groupoid.inv f,Groupoid.comp_inv f,Groupoid.inv_comp f⟩

theorem kg_family_associator_naturality {a : Parameters} {A A' B B' C C' : KGFamilyObject a}
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C') :
    kgInternalTensor (kgInternalTensor f g) h ≫ kgFamilyAssociator A' B' C' =
      kgFamilyAssociator A B C ≫ kgInternalTensor f (kgInternalTensor g h) := by
  apply kg_internal_arrow_ext
  have equality :
      (kgInternalTensor (kgInternalTensor f g) h ≫ kgFamilyAssociator A' B' C').isometry.toLinearMap =
      (kgFamilyAssociator A B C ≫ kgInternalTensor f (kgInternalTensor g h)).isometry.toLinearMap := by
    apply TensorProduct.ext_threefold
    intro x y z
    rfl
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun equality)

theorem kg_family_left_unitor_naturality {a : Parameters} {A B : KGFamilyObject a} (f : A ⟶ B) :
    kgInternalTensor (𝟙 (kgFamilyUnit a)) f ≫ kgFamilyLeftUnitor B=kgFamilyLeftUnitor A ≫ f := by
  apply kg_internal_arrow_ext
  have equality :
      (kgInternalTensor (𝟙 (kgFamilyUnit a)) f ≫ kgFamilyLeftUnitor B).isometry.toLinearMap =
      (kgFamilyLeftUnitor A ≫ f).isometry.toLinearMap := by
    apply TensorProduct.ext'
    intro c x
    change ℂ at c
    change (c : ℂ) • f.isometry x=f.isometry ((c : ℂ) • x)
    exact (f.isometry.map_smul (c : ℂ) x).symm
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun equality)

theorem kg_family_symmetry_naturality {a : Parameters} {A A' B B' : KGFamilyObject a}
    (f : A ⟶ A') (g : B ⟶ B') :
    kgInternalTensor f g ≫ kgFamilySymmetry A' B'=kgFamilySymmetry A B ≫ kgInternalTensor g f := by
  apply kg_internal_arrow_ext
  have equality :
      (kgInternalTensor f g ≫ kgFamilySymmetry A' B').isometry.toLinearMap =
      (kgFamilySymmetry A B ≫ kgInternalTensor g f).isometry.toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun equality)

theorem kg_family_pentagon {a : Parameters} (A B C D : KGFamilyObject a) :
    kgFamilyAssociator (kgFamilyTensor A B) C D ≫ kgFamilyAssociator A B (kgFamilyTensor C D) =
      kgInternalTensor (kgFamilyAssociator A B C) (𝟙 D) ≫
        kgFamilyAssociator A (kgFamilyTensor B C) D ≫
          kgInternalTensor (𝟙 A) (kgFamilyAssociator B C D) := by
  apply kg_internal_arrow_ext
  ext z
  exact LinearMap.congr_fun (kg_raw_tensor_pentagon
    (KGFamilyCarrier A) (KGFamilyCarrier B) (KGFamilyCarrier C) (KGFamilyCarrier D)) z

theorem kg_family_triangle {a : Parameters} (A B : KGFamilyObject a) :
    kgFamilyAssociator A (kgFamilyUnit a) B ≫ kgInternalTensor (𝟙 A) (kgFamilyLeftUnitor B) =
      kgInternalTensor (kgFamilyRightUnitor A) (𝟙 B) := by
  apply kg_internal_arrow_ext
  have equality :
      (kgFamilyAssociator A (kgFamilyUnit a) B ≫ kgInternalTensor (𝟙 A) (kgFamilyLeftUnitor B)).isometry.toLinearMap =
      (kgInternalTensor (kgFamilyRightUnitor A) (𝟙 B)).isometry.toLinearMap := by
    apply TensorProduct.ext_threefold
    intro x c y
    change ℂ at c
    change x ⊗ₜ[ℂ] ((c : ℂ) • y)=((c : ℂ) • x) ⊗ₜ[ℂ] y
    rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul']
  exact LinearIsometryEquiv.ext (LinearMap.congr_fun equality)

theorem kg_family_symmetry_involutive {a : Parameters} (A B : KGFamilyObject a) :
    kgFamilySymmetry A B ≫ kgFamilySymmetry B A=𝟙 (kgFamilyTensor A B) := by
  apply kg_internal_arrow_ext
  ext z
  exact LinearMap.congr_fun (kg_raw_tensor_symmetry_involutive (KGFamilyCarrier A) (KGFamilyCarrier B)) z

theorem kg_family_hexagon {a : Parameters} (A B C : KGFamilyObject a) :
    kgFamilyAssociator A B C ≫ kgFamilySymmetry A (kgFamilyTensor B C) ≫ kgFamilyAssociator B C A =
      kgInternalTensor (kgFamilySymmetry A B) (𝟙 C) ≫ kgFamilyAssociator B A C ≫
        kgInternalTensor (𝟙 B) (kgFamilySymmetry A C) := by
  apply kg_internal_arrow_ext
  ext z
  exact LinearMap.congr_fun (kg_raw_tensor_hexagon (KGFamilyCarrier A) (KGFamilyCarrier B)
    (KGFamilyCarrier C)) z

end AASCKleinGordon
