import KGSpatialSourceComposition

/-! Actual canonical comparison lifts and their full original record/reference
naturality. A general old internal arrow is not declared to restrict to the
chosen source core without a proved vector square. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace CategoryTheory AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KGSpatialComparisonLift (a : Parameters) (A B : KGComparisonObject) where
  original : (⟨A⟩ : KGFamilyObject a) ⟶ ⟨B⟩
  spatial : KGSpatialFamilyCarrier a A ≃ₗᵢ[ℂ] KGSpatialFamilyCarrier a B
  vector_square : ∀ x, kgSpatialFamilyOriginalEmbedding a B (spatial x) =
    original.isometry (kgSpatialFamilyOriginalEmbedding a A x)

theorem kg_spatial_comparison_lift_pure_square (a : Parameters) (A B : KGComparisonObject)
    (f : KGSpatialComparisonLift a A B) (x : PureVector (KGSpatialFamilyCarrier a A)) :
    kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a B) (PureVector.mapUnitary f.spatial x) =
      PureVector.mapUnitary f.original.isometry
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x) :=
  Subtype.ext (f.vector_square x.val)

theorem kg_spatial_comparison_lift_complete_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (f : KGSpatialComparisonLift a A B) (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : KGFamilyQuestion a Ω ⟨B⟩) :
    kgSpatialFamilyRecord a s Ω B (rayMap _ (PureVector.mapUnitary f.spatial x)) q =
      kgSpatialFamilyRecord a s Ω A (rayMap _ x) (kgFamilyQuestionPullback f.original q) := by
  rw [kg_spatial_family_complete_original_record,kg_spatial_family_complete_original_record,
    kg_spatial_comparison_lift_pure_square]
  exact kg_family_arrow_output a s Ω f.original _ q

theorem kg_spatial_comparison_lift_reference (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (f : KGSpatialComparisonLift a A B) (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω ⟨B⟩)) :
    kgSpatialFamilyReference a s Ω B (rayMap _ (PureVector.mapUnitary f.spatial x)) q =
      kgSpatialFamilyReference a s Ω A (rayMap _ x)
        (mapRegisteredQuestion (kgFamilyQuestionPullback f.original) q) := by
  rw [kg_spatial_family_reference_square,kg_spatial_family_reference_square,
    kg_spatial_comparison_lift_pure_square]
  exact (kg_raw_arrow_reference a s Ω f.original _ q).symm

theorem kg_spatial_comparison_lift_first_failure (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (f : KGSpatialComparisonLift a A B) (x : PureVector (KGSpatialFamilyCarrier a A))
    (word : List (KGFamilyQuestion a Ω ⟨B⟩)) :
    kgFirstFailure (kgSpatialFamilyRecord a s Ω A (rayMap _ x))
      (word.map (kgFamilyQuestionPullback f.original)) =
      kgFirstFailure (kgSpatialFamilyRecord a s Ω B
        (rayMap _ (PureVector.mapUnitary f.spatial x))) word :=
  kg_first_failure_map _ _ _
    (fun q => (kg_spatial_comparison_lift_complete_record a s Ω A B f x q).symm) word

def kgSpatialAssociatorLift (a : Parameters) (A B C : KGComparisonObject) :
    KGSpatialComparisonLift a (.tensor (.tensor A B) C) (.tensor A (.tensor B C)) where
  original := kgFamilyAssociator ⟨A⟩ ⟨B⟩ ⟨C⟩
  spatial := TensorProduct.assocIsometry ℂ _ _ _
  vector_square := kg_spatial_family_embedding_associator a A B C

def kgSpatialSymmetryLift (a : Parameters) (A B : KGComparisonObject) :
    KGSpatialComparisonLift a (.tensor A B) (.tensor B A) where
  original := kgFamilySymmetry ⟨A⟩ ⟨B⟩
  spatial := TensorProduct.commIsometry ℂ _ _
  vector_square := kg_spatial_family_embedding_symmetry a A B

def kgSpatialLeftUnitorLift (a : Parameters) (A : KGComparisonObject) :
    KGSpatialComparisonLift a (.tensor .unit A) A where
  original := kgFamilyLeftUnitor ⟨A⟩
  spatial := TensorProduct.lidIsometry ℂ _
  vector_square := kg_spatial_family_embedding_left_unitor a A

def kgSpatialRightUnitorLift (a : Parameters) (A : KGComparisonObject) :
    KGSpatialComparisonLift a (.tensor A .unit) A where
  original := kgFamilyRightUnitor ⟨A⟩
  spatial := (TensorProduct.commIsometry ℂ _ _).trans (TensorProduct.lidIsometry ℂ _)
  vector_square x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x c =>
      change ℂ at c
      change kgSpatialFamilyOriginalEmbedding a A (c • x) =
        c • kgSpatialFamilyOriginalEmbedding a A x
      exact (kgSpatialFamilyOriginalEmbedding a A).map_smul c x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

def kgSpatialIdentityLift (a : Parameters) (A : KGComparisonObject) :
    KGSpatialComparisonLift a A A where
  original := kgInternalIdentity (⟨A⟩ : KGFamilyObject a)
  spatial := LinearIsometryEquiv.refl ℂ _
  vector_square _ := rfl

def kgSpatialComposeLift {a : Parameters} {A B C : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) (g : KGSpatialComparisonLift a B C) :
    KGSpatialComparisonLift a A C where
  original := f.original ≫ g.original
  spatial := f.spatial.trans g.spatial
  vector_square x := by
    change kgSpatialFamilyOriginalEmbedding a C (g.spatial (f.spatial x)) = _
    rw [g.vector_square,f.vector_square]
    rfl

def kgSpatialTensorLift {a : Parameters} {A B C D : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) (g : KGSpatialComparisonLift a C D) :
    KGSpatialComparisonLift a (.tensor A C) (.tensor B D) where
  original := kgInternalTensor f.original g.original
  spatial := TensorProduct.congrIsometry f.spatial g.spatial
  vector_square x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change (kgSpatialFamilyOriginalEmbedding a B (f.spatial x)) ⊗ₜ[ℂ]
        (kgSpatialFamilyOriginalEmbedding a D (g.spatial y)) =
        f.original.isometry (kgSpatialFamilyOriginalEmbedding a A x) ⊗ₜ[ℂ]
          g.original.isometry (kgSpatialFamilyOriginalEmbedding a C y)
      rw [f.vector_square,g.vector_square]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem kg_spatial_lift_faithful (a : Parameters) (A B : KGComparisonObject)
    (f g : KGSpatialComparisonLift a A B) (h : f.original = g.original) :
    f.spatial = g.spatial := by
  ext x
  apply (kgSpatialFamilyOriginalEmbedding a B).injective
  rw [f.vector_square,g.vector_square,h]

theorem kg_spatial_composition_pentagon (a : Parameters) (A B C D : KGComparisonObject) :
    (kgSpatialComposeLift (kgSpatialAssociatorLift a (.tensor A B) C D)
      (kgSpatialAssociatorLift a A B (.tensor C D))).spatial =
      (kgSpatialComposeLift
        (kgSpatialComposeLift
          (kgSpatialTensorLift (kgSpatialAssociatorLift a A B C) (kgSpatialIdentityLift a D))
          (kgSpatialAssociatorLift a A (.tensor B C) D))
        (kgSpatialTensorLift (kgSpatialIdentityLift a A) (kgSpatialAssociatorLift a B C D))).spatial := by
  apply kg_spatial_lift_faithful
  exact kg_family_pentagon (a := a) ⟨A⟩ ⟨B⟩ ⟨C⟩ ⟨D⟩

theorem kg_spatial_composition_triangle (a : Parameters) (A B : KGComparisonObject) :
    (kgSpatialComposeLift (kgSpatialAssociatorLift a A .unit B)
      (kgSpatialTensorLift (kgSpatialIdentityLift a A) (kgSpatialLeftUnitorLift a B))).spatial =
      (kgSpatialTensorLift (kgSpatialRightUnitorLift a A) (kgSpatialIdentityLift a B)).spatial := by
  apply kg_spatial_lift_faithful
  exact kg_family_triangle (a := a) ⟨A⟩ ⟨B⟩

theorem kg_spatial_composition_hexagon (a : Parameters) (A B C : KGComparisonObject) :
    (kgSpatialComposeLift
      (kgSpatialComposeLift (kgSpatialAssociatorLift a A B C)
        (kgSpatialSymmetryLift a A (.tensor B C))) (kgSpatialAssociatorLift a B C A)).spatial =
      (kgSpatialComposeLift
        (kgSpatialComposeLift
          (kgSpatialTensorLift (kgSpatialSymmetryLift a A B) (kgSpatialIdentityLift a C))
          (kgSpatialAssociatorLift a B A C))
        (kgSpatialTensorLift (kgSpatialIdentityLift a B) (kgSpatialSymmetryLift a A C))).spatial := by
  apply kg_spatial_lift_faithful
  exact kg_family_hexagon (a := a) ⟨A⟩ ⟨B⟩ ⟨C⟩

end AASCKleinGordon
