import KGSpatialStandingTransport

/-! The entire finite algebraic independent-composition family of the declared
spatial source core. All tensor vectors, including entangled finite sums, carry
the inherited original questions. No completed tensor carrier is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgSpatialFamilySpace (a : Parameters) : KGComparisonObject → KGInnerCarrier
  | .unit => kgInnerCarrierOf ℂ
  | .kg => kgInnerCarrierOf (kgOriginalSpatialCore a)
  | .tensor A B => kgInnerCarrierOf (kgSpatialFamilySpace a A ⊗[ℂ] kgSpatialFamilySpace a B)

abbrev KGSpatialFamilyCarrier (a : Parameters) (A : KGComparisonObject) :=
  kgSpatialFamilySpace a A

def kgSpatialFamilyOriginalEmbedding (a : Parameters) :
    (A : KGComparisonObject) → KGSpatialFamilyCarrier a A →ₗᵢ[ℂ] KGComparisonCarrier a A
  | .unit => LinearIsometry.id
  | .kg => kgSpatialCoreOriginalEmbedding a
  | .tensor A B => TensorProduct.mapIsometry
      (kgSpatialFamilyOriginalEmbedding a A) (kgSpatialFamilyOriginalEmbedding a B)

def kgSpatialFamilyOriginalRay (a : Parameters) (A : KGComparisonObject) :
    PhysicalRay (KGSpatialFamilyCarrier a A) → PhysicalRay (KGComparisonCarrier a A) :=
  kgRayIsometryMap (kgSpatialFamilyOriginalEmbedding a A)

def kgSpatialFamilyRecord (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) (r : PhysicalRay (KGSpatialFamilyCarrier a A)) :=
  kgW9StandingRecord a s Ω ⟨A⟩ (kgSpatialFamilyOriginalRay a A r)

theorem kg_spatial_family_record_faithful (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject) :
    Function.Injective (kgSpatialFamilyRecord a s Ω A) :=
  (kg_w9_standing_record_faithful a s Ω ⟨A⟩).comp
    (kg_ray_isometry_injective (kgSpatialFamilyOriginalEmbedding a A))

theorem kg_spatial_family_complete_original_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGFamilyQuestion a Ω ⟨A⟩) :
    kgSpatialFamilyRecord a s Ω A (rayMap _ x) q =
      kgFamilyOutput a s Ω ⟨A⟩
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x) q :=
  kg_w9_standing_complete_record a s Ω ⟨A⟩ _ q

theorem kg_spatial_family_first_failure (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (word : List (KGFamilyQuestion a Ω ⟨A⟩)) :
    kgFirstFailure (kgSpatialFamilyRecord a s Ω A (rayMap _ x)) word =
      kgFirstFailure (kgFamilyOutput a s Ω ⟨A⟩
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x)) word := by
  congr 1
  funext q
  exact kg_spatial_family_complete_original_record a s Ω A x q

def kgSpatialFamilyReference (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) (r : PhysicalRay (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω ⟨A⟩)) :=
  (kgRawRegisteredOrbit a s Ω ⟨A⟩).standingReferences.referenceAt
    (kgSpatialFamilyOriginalRay a A r) q

theorem kg_spatial_family_reference_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω ⟨A⟩)) :
    kgSpatialFamilyReference a s Ω A (rayMap _ x) q =
      (kgRawRegisteredOrbit a s Ω ⟨A⟩).references.referenceAt
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x) q :=
  (kgRawRegisteredOrbit a s Ω ⟨A⟩).standing_reference_square _ q

theorem kg_spatial_family_tensor_original_square (a : Parameters)
    (A B : KGComparisonObject) (x : PureVector (KGSpatialFamilyCarrier a A))
    (y : PureVector (KGSpatialFamilyCarrier a B)) :
    kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a (.tensor A B)) (kgRawTensor x y) =
      kgRawTensor (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x)
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a B) y) := by
  apply Subtype.ext
  rfl

theorem kg_spatial_family_tensor_weights (a : Parameters) (A B : KGComparisonObject)
    (x z : PureVector (KGSpatialFamilyCarrier a A))
    (y w : PureVector (KGSpatialFamilyCarrier a B)) :
    transitionProbability
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a (.tensor A B)) (kgRawTensor x y))
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a (.tensor A B)) (kgRawTensor z w)) =
      transitionProbability x z * transitionProbability y w := by
  rw [kg_pure_isometry_weight,kg_raw_tensor_weights_multiply]

theorem kg_spatial_family_product_right_complete_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (y : PureVector (KGSpatialFamilyCarrier a B)) (K : KGExtraction a ⟨A⟩)
    (q : WickMetricPathRoleProtocol Ω) :
    kgSpatialFamilyRecord a s Ω (.tensor A B) (rayMap _ (kgRawTensor x y))
      (.original (.right K ((kgSpatialFamilyOriginalEmbedding a B) y.val)) q) =
      kgSpatialFamilyRecord a s Ω A (rayMap _ x) (.original K q) := by
  rw [kg_spatial_family_complete_original_record,
    kg_spatial_family_complete_original_record,kg_spatial_family_tensor_original_square]
  exact kg_product_right_original_record a s Ω ⟨A⟩ ⟨B⟩ _ _ K q

theorem kg_spatial_family_product_left_complete_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (y : PureVector (KGSpatialFamilyCarrier a B)) (K : KGExtraction a ⟨B⟩)
    (q : WickMetricPathRoleProtocol Ω) :
    kgSpatialFamilyRecord a s Ω (.tensor A B) (rayMap _ (kgRawTensor x y))
      (.original (.left ((kgSpatialFamilyOriginalEmbedding a A) x.val) K) q) =
      kgSpatialFamilyRecord a s Ω B (rayMap _ y) (.original K q) := by
  rw [kg_spatial_family_complete_original_record,
    kg_spatial_family_complete_original_record,kg_spatial_family_tensor_original_square]
  exact kg_product_left_original_record a s Ω ⟨A⟩ ⟨B⟩ _ _ K q

theorem kg_spatial_family_embedding_associator (a : Parameters)
    (A B C : KGComparisonObject)
    (x : (KGSpatialFamilyCarrier a A ⊗[ℂ] KGSpatialFamilyCarrier a B) ⊗[ℂ]
      KGSpatialFamilyCarrier a C) :
    kgSpatialFamilyOriginalEmbedding a (.tensor A (.tensor B C))
      (TensorProduct.assoc ℂ _ _ _ x) =
      TensorProduct.assoc ℂ _ _ _
        (kgSpatialFamilyOriginalEmbedding a (.tensor (.tensor A B) C) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul ab c =>
    induction ab using TensorProduct.induction_on with
    | zero => simp only [map_zero,TensorProduct.zero_tmul]
    | tmul a b => rfl
    | add ab ab' h h' => simpa only [TensorProduct.add_tmul,map_add] using congrArg₂ (· + ·) h h'
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem kg_spatial_family_embedding_symmetry (a : Parameters)
    (A B : KGComparisonObject)
    (x : KGSpatialFamilyCarrier a A ⊗[ℂ] KGSpatialFamilyCarrier a B) :
    kgSpatialFamilyOriginalEmbedding a (.tensor B A) (TensorProduct.comm ℂ _ _ x) =
      TensorProduct.comm ℂ _ _ (kgSpatialFamilyOriginalEmbedding a (.tensor A B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem kg_spatial_family_tensor_ray_square (a : Parameters)
    (A B : KGComparisonObject) (r : PhysicalRay (KGSpatialFamilyCarrier a A))
    (u : PhysicalRay (KGSpatialFamilyCarrier a B)) :
    kgSpatialFamilyOriginalRay a (.tensor A B) (kgTensorRay r u) =
      kgTensorRay (kgSpatialFamilyOriginalRay a A r) (kgSpatialFamilyOriginalRay a B u) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    induction u using Quotient.inductionOn with
    | _ y => rfl

theorem kg_spatial_family_tensor_ray_regular (a : Parameters) (A B : KGComparisonObject) :
    Continuous (fun p : PhysicalRay (KGSpatialFamilyCarrier a A) ×
      PhysicalRay (KGSpatialFamilyCarrier a B) => kgTensorRay p.1 p.2) :=
  kg_tensor_ray_joint_continuous

theorem kg_spatial_family_embedding_left_unitor (a : Parameters)
    (A : KGComparisonObject) (x : ℂ ⊗[ℂ] KGSpatialFamilyCarrier a A) :
    kgSpatialFamilyOriginalEmbedding a A (TensorProduct.lid ℂ _ x) =
      TensorProduct.lid ℂ _ (kgSpatialFamilyOriginalEmbedding a (.tensor .unit A) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x => exact (kgSpatialFamilyOriginalEmbedding a A).map_smul c x
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem kg_spatial_family_regional_record (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGComparisonObject)
    (r : PhysicalRay (KGSpatialFamilyCarrier a A)) (q : KGFamilyQuestion a Ω ⟨A⟩) :
    kgSpatialFamilyRecord a s V A r (kgFamilyQuestionExtend h q) =
      kgSpatialFamilyRecord a s Ω A r q :=
  kg_standing_region_record a s h ⟨A⟩ (kgSpatialFamilyOriginalRay a A r) q

theorem kg_spatial_family_scalar_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGFamilyQuestion a Ω ⟨A⟩) :
    kgSpatialFamilyRecord a s Ω A (rayMap _ (PureVector.smul c hc x)) q =
      kgSpatialFamilyRecord a s Ω A (rayMap _ x) q := by
  rw [kg_spatial_family_complete_original_record,kg_spatial_family_complete_original_record,
    kg_pure_isometry_scalar]
  exact kg_family_output_scalar a s Ω ⟨A⟩ c hc _ q

end AASCKleinGordon
