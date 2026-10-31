import KGNRSourceCoreFlow
import KGSpatialSourceComposition

/-! Complete original records at the actual NR-evolved source state. These
theorems do not assert fixed-question invariance or finite-c record equality. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local irreducible] kgOriginalSpatialCoreEquiv kgPhysicalSpatialUnitary

def kgOneCoreOriginalEmbedding (a : Parameters) :
    kgOriginalOneCore a →ₗᵢ[ℂ] fockCoreDomain a where
  toLinearMap := (kgOriginalOneCore a).subtype
  norm_map' _ := rfl

def kgNRSpatialOriginalPreparation (a : Parameters) (t : ℝ)
    (x : PureVector (kgOriginalSpatialCore a)) : PureVector (fockCoreDomain a) :=
  kgPureIsometryMap (H := kgOriginalSpatialCore a) (K := fockCoreDomain a)
    ((kgOneCoreOriginalEmbedding a).comp
      (((kgOriginalSpatialCoreEquiv a).symm).trans
        (kgNROriginalOneCoreFlow a t)).toLinearIsometry) x

theorem kg_nr_spatial_core_original_preparation_square (a : Parameters) (t : ℝ)
    (x : PureVector (kgOriginalSpatialCore a)) :
    kgPureIsometryMap (kgSpatialCoreOriginalEmbedding a)
      (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x) =
      kgNRSpatialOriginalPreparation a t x := by
  apply Subtype.ext
  change ((kgOriginalSpatialCoreEquiv a).symm
    (kgOriginalSpatialCoreEquiv a
      (kgNROriginalOneCoreFlow a t ((kgOriginalSpatialCoreEquiv a).symm x.val)))).val = _
  exact congrArg (fun y : kgOriginalOneCore a => y.val)
    ((kgOriginalSpatialCoreEquiv a).symm_apply_apply
      (kgNROriginalOneCoreFlow a t ((kgOriginalSpatialCoreEquiv a).symm x.val)))

theorem kg_nr_spatial_evolved_complete_original_record (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgSpatialSourceRecord a s Ω
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x)) q =
      kgFamilyOutput a s Ω (kgOriginalObject a) (kgNRSpatialOriginalPreparation a t x) q := by
  rw [kg_spatial_source_complete_record,kg_nr_spatial_core_original_preparation_square]

theorem kg_nr_spatial_evolved_original_reference (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    kgSpatialSourceReference a s Ω
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x)) q =
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.referenceAt
        (kgNRSpatialOriginalPreparation a t x) q := by
  rw [kg_spatial_reference_original_square,kg_nr_spatial_core_original_preparation_square]

theorem kg_nr_spatial_evolved_original_first_failure (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (word : List (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    kgFirstFailure (kgSpatialSourceRecord a s Ω
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x))) word =
      kgFirstFailure (kgFamilyOutput a s Ω (kgOriginalObject a)
        (kgNRSpatialOriginalPreparation a t x)) word := by
  congr 1
  funext q
  exact kg_nr_spatial_evolved_complete_original_record a s t Ω x q

theorem kg_nr_spatial_evolved_original_source_attachment (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a)) :
    kgW9OriginalResponse a s Ω
      (rayMap _ (kgNRSpatialOriginalPreparation a t x)) =
      (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
        (wickCommonRoleSourcePresentation a s Ω
          (kgOriginalQuantumToRay a (rayMap _ (kgNRSpatialOriginalPreparation a t x)))))).val :=
  kg_w9_complete_original_source_square a s Ω _

theorem kg_nr_spatial_evolved_value_is_full_flow (a : Parameters) (t : ℝ)
    (x : PureVector (kgOriginalSpatialCore a)) :
    (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x).val.val =
      kgNRSpatialFreeFlow a t x.val.val := kg_nr_spatial_core_flow_full_value a t x.val

attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgNRSpatialFamilyFlow (a : Parameters) (t : ℝ) : (A : KGComparisonObject) →
    KGSpatialFamilyCarrier a A ≃ₗᵢ[ℂ] KGSpatialFamilyCarrier a A
  | .unit => LinearIsometryEquiv.refl ℂ ℂ
  | .kg => kgNRSpatialCoreFlow a t
  | .tensor A B => TensorProduct.congrIsometry
      (kgNRSpatialFamilyFlow a t A) (kgNRSpatialFamilyFlow a t B)

theorem kg_nr_spatial_family_flow_zero (a : Parameters) (A : KGComparisonObject)
    (x : KGSpatialFamilyCarrier a A) : kgNRSpatialFamilyFlow a 0 A x = x := by
  induction A with
  | unit => rfl
  | kg => exact kg_nr_spatial_core_flow_zero a x
  | tensor A B hA hB =>
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul x y =>
      change kgNRSpatialFamilyFlow a 0 A x ⊗ₜ[ℂ] kgNRSpatialFamilyFlow a 0 B y = _
      rw [hA x,hB y]
    | add x y hx hy => rw [map_add,hx,hy]

theorem kg_nr_spatial_family_flow_add (a : Parameters) (t s : ℝ)
    (A : KGComparisonObject) (x : KGSpatialFamilyCarrier a A) :
    kgNRSpatialFamilyFlow a (t+s) A x =
      kgNRSpatialFamilyFlow a t A (kgNRSpatialFamilyFlow a s A x) := by
  induction A with
  | unit => rfl
  | kg => exact kg_nr_spatial_core_flow_add a t s x
  | tensor A B hA hB =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      change kgNRSpatialFamilyFlow a (t+s) A x ⊗ₜ[ℂ] kgNRSpatialFamilyFlow a (t+s) B y =
        kgNRSpatialFamilyFlow a t A (kgNRSpatialFamilyFlow a s A x) ⊗ₜ[ℂ]
          kgNRSpatialFamilyFlow a t B (kgNRSpatialFamilyFlow a s B y)
      rw [hA x,hB y]
    | add x y hx hy => simp only [map_add,hx,hy]

theorem kg_nr_spatial_family_pure_zero (a : Parameters) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) :
    PureVector.mapUnitary (kgNRSpatialFamilyFlow a 0 A) x = x :=
  Subtype.ext (kg_nr_spatial_family_flow_zero a A x.val)

theorem kg_nr_spatial_family_pure_add (a : Parameters) (t s : ℝ) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) :
    PureVector.mapUnitary (kgNRSpatialFamilyFlow a (t+s) A) x =
      PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A)
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a s A) x) :=
  Subtype.ext (kg_nr_spatial_family_flow_add a t s A x.val)

theorem kg_nr_spatial_family_flow_tensor (a : Parameters) (t : ℝ)
    (A B : KGComparisonObject) (x : PureVector (KGSpatialFamilyCarrier a A))
    (y : PureVector (KGSpatialFamilyCarrier a B)) :
    PureVector.mapUnitary (kgNRSpatialFamilyFlow a t (.tensor A B)) (kgRawTensor x y) =
      kgRawTensor (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x)
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t B) y) := by
  apply Subtype.ext
  rfl

theorem kg_nr_spatial_family_evolved_complete_record (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGFamilyQuestion a Ω ⟨A⟩) :
    kgSpatialFamilyRecord a s Ω A
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x)) q =
      kgFamilyOutput a s Ω ⟨A⟩ (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A)
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x)) q :=
  kg_spatial_family_complete_original_record a s Ω A _ q

end AASCKleinGordon
