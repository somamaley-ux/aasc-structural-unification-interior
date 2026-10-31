import KGNRReceivingQuestions

/-! The actual faithful projection into the full spatial L2 envelope and its
finite algebraic tensor family. This does not extend all old records to L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgNRFullFamilySpace : KGComparisonObject → KGInnerCarrier
  | .unit => kgInnerCarrierOf ℂ
  | .kg => kgInnerCarrierOf KGNRSpatialHilbert
  | .tensor A B => kgInnerCarrierOf (kgNRFullFamilySpace A ⊗[ℂ] kgNRFullFamilySpace B)

def kgNRFullSpatialEmbedding (a : Parameters) : kgOriginalSpatialCore a →ₗᵢ[ℂ] KGNRSpatialHilbert where
  toLinearMap := (kgOriginalSpatialCore a).subtype
  norm_map' _ := rfl

def kgNRFullFamilyEmbedding (a : Parameters) : (A : KGComparisonObject) →
    KGSpatialFamilyCarrier a A →ₗᵢ[ℂ] kgNRFullFamilySpace A
  | .unit => LinearIsometry.id
  | .kg => kgNRFullSpatialEmbedding a
  | .tensor A B => TensorProduct.mapIsometry
      (kgNRFullFamilyEmbedding a A) (kgNRFullFamilyEmbedding a B)

def kgNRFullProjection (a : Parameters) (A : KGComparisonObject) :
    PhysicalRay (KGSpatialFamilyCarrier a A) → PhysicalRay (kgNRFullFamilySpace A) :=
  kgRayIsometryMap (kgNRFullFamilyEmbedding a A)

theorem kg_nr_full_projection_faithful (a : Parameters) (A : KGComparisonObject) :
    Function.Injective (kgNRFullProjection a A) := kg_ray_isometry_injective _

theorem kg_nr_full_projection_original_standing (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x y : PureVector (KGSpatialFamilyCarrier a A)) :
    (kgRawRegisteredOrbit a s Ω ⟨A⟩).SameRegisteredStanding
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x)
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) y) ↔
      kgNRFullProjection a A (rayMap _ x) = kgNRFullProjection a A (rayMap _ y) := by
  rw [← kg_nr_receiving_same_original_registered_standing,
    kg_nr_receiving_registered_standing_exact]
  exact ⟨congrArg (kgNRFullProjection a A),fun h => kg_nr_full_projection_faithful a A h⟩

theorem kg_nr_full_projection_weights (a : Parameters) (A : KGComparisonObject)
    (x y : PureVector (KGSpatialFamilyCarrier a A)) :
    transitionProbability (kgPureIsometryMap (kgNRFullFamilyEmbedding a A) x)
      (kgPureIsometryMap (kgNRFullFamilyEmbedding a A) y) = transitionProbability x y :=
  kg_pure_isometry_weight _ x y

theorem kg_nr_full_projection_tensor (a : Parameters) (A B : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (y : PureVector (KGSpatialFamilyCarrier a B)) :
    kgPureIsometryMap (kgNRFullFamilyEmbedding a (.tensor A B)) (kgRawTensor x y) =
      kgRawTensor (kgPureIsometryMap (kgNRFullFamilyEmbedding a A) x)
        (kgPureIsometryMap (kgNRFullFamilyEmbedding a B) y) := Subtype.ext rfl

def kgNRFullFamilyFlow (a : Parameters) (t : ℝ) : (A : KGComparisonObject) →
    kgNRFullFamilySpace A ≃ₗᵢ[ℂ] kgNRFullFamilySpace A
  | .unit => LinearIsometryEquiv.refl ℂ ℂ
  | .kg => kgNRSpatialFreeFlow a t
  | .tensor A B => TensorProduct.congrIsometry (kgNRFullFamilyFlow a t A) (kgNRFullFamilyFlow a t B)

theorem kg_nr_full_projection_flow_square (a : Parameters) (t : ℝ) (A : KGComparisonObject)
    (x : KGSpatialFamilyCarrier a A) :
    kgNRFullFamilyEmbedding a A (kgNRSpatialFamilyFlow a t A x) =
      kgNRFullFamilyFlow a t A (kgNRFullFamilyEmbedding a A x) := by
  induction A with
  | unit => rfl
  | kg => exact kg_nr_spatial_core_flow_full_value a t x
  | tensor A B hA hB =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change kgNRFullFamilyEmbedding a A (kgNRSpatialFamilyFlow a t A x) ⊗ₜ[ℂ]
        kgNRFullFamilyEmbedding a B (kgNRSpatialFamilyFlow a t B y) = _
      rw [hA x,hB y]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

theorem kg_nr_full_projection_ray_continuation (a : Parameters) (t : ℝ)
    (A : KGComparisonObject) (x : PureVector (KGSpatialFamilyCarrier a A)) :
    kgNRFullProjection a A
      (unitaryRayMap (kgNRSpatialFamilyFlow a t A) (rayMap _ x)) =
      unitaryRayMap (kgNRFullFamilyFlow a t A) (kgNRFullProjection a A (rayMap _ x)) := by
  apply congrArg (rayMap _)
  exact Subtype.ext (kg_nr_full_projection_flow_square a t A x.val)

end AASCKleinGordon
