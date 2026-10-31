import KGPhysicalSpatialUnitary
import KGConstraintStandingSource

/-! Receiving transport on the actual image of the admitted original one-particle
core. Original records are retained through an injective isometry. This does not
extend those records to the completion merely from density. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace
attribute [local irreducible] kgPhysicalSpatialUnitary kgIsolatedSpatialUnitary

def kgOriginalOneCore (a : Parameters) : Submodule ℂ (fockCoreDomain a) :=
  (wickIsolatedOneParticleSpace a).comap (fockCoreDomain a).subtype

def kgOriginalOneCoreToIsolated (a : Parameters) :
    kgOriginalOneCore a →ₗᵢ[ℂ] wickIsolatedOneParticleSpace a where
  toLinearMap :=
    { toFun := fun x => ⟨x.val.val,x.prop⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  norm_map' x := rfl

def kgOriginalOneCoreSpatialEmbedding (a : Parameters) :
    kgOriginalOneCore a →ₗᵢ[ℂ] KGNRSpatialHilbert :=
  (kgIsolatedSpatialUnitary a).toLinearIsometry.comp (kgOriginalOneCoreToIsolated a)

def kgOriginalSpatialCore (a : Parameters) : Submodule ℂ KGNRSpatialHilbert :=
  (kgOriginalOneCoreSpatialEmbedding a).toLinearMap.range

def kgOriginalSpatialCoreEquiv (a : Parameters) :
    kgOriginalOneCore a ≃ₗᵢ[ℂ] kgOriginalSpatialCore a :=
  (kgOriginalOneCoreSpatialEmbedding a).equivRange

def kgSpatialCoreOriginalEmbedding (a : Parameters) :
    kgOriginalSpatialCore a →ₗᵢ[ℂ] fockCoreDomain a where
  toLinearMap := (kgOriginalOneCore a).subtype.comp
    (kgOriginalSpatialCoreEquiv a).symm.toLinearMap
  norm_map' x := (kgOriginalSpatialCoreEquiv a).symm.norm_map x

section IsometryRays
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def kgPureIsometryMap (L : H →ₗᵢ[ℂ] K) (x : PureVector H) : PureVector K :=
  ⟨L x.val,by intro h; apply x.prop; exact L.injective (h.trans L.map_zero.symm)⟩

theorem kg_pure_isometry_scalar (L : H →ₗᵢ[ℂ] K) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector H) :
    kgPureIsometryMap L (PureVector.smul c hc x) =
      PureVector.smul c hc (kgPureIsometryMap L x) :=
  Subtype.ext (L.map_smul c x.val)

def kgRayIsometryMap (L : H →ₗᵢ[ℂ] K) : PhysicalRay H → PhysicalRay K :=
  Quotient.map (kgPureIsometryMap L) (by
    rintro x y ⟨c,hc,h⟩
    refine ⟨c,hc,?_⟩
    change c • L x.val = L y.val
    rw [← L.map_smul,h])

theorem kg_ray_isometry_injective (L : H →ₗᵢ[ℂ] K) :
    Function.Injective (kgRayIsometryMap L) := by
  intro r t
  induction r using Quotient.inductionOn with
  | _ x =>
    induction t using Quotient.inductionOn with
    | _ y =>
      intro h
      obtain ⟨c,hc,he⟩ := Quotient.exact h
      apply Quotient.sound
      refine ⟨c,hc,L.injective ?_⟩
      exact (L.map_smul c x.val).trans he

theorem kg_pure_isometry_weight (L : H →ₗᵢ[ℂ] K) (x y : PureVector H) :
    transitionProbability (kgPureIsometryMap L x) (kgPureIsometryMap L y) =
      transitionProbability x y := by
  simp only [transitionProbability,kgPureIsometryMap,L.inner_map_map,L.norm_map]

end IsometryRays

def kgSpatialOriginalRay (a : Parameters) :
    PhysicalRay (kgOriginalSpatialCore a) → PhysicalRay (fockCoreDomain a) :=
  kgRayIsometryMap (kgSpatialCoreOriginalEmbedding a)

def kgSpatialSourceRecord (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (kgOriginalSpatialCore a)) :
    KGFamilyQuestion a Ω (kgOriginalObject a) → KGFamilyReadout :=
  kgW9StandingRecord a s Ω (kgOriginalObject a) (kgSpatialOriginalRay a r)

theorem kg_spatial_source_record_faithful (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Function.Injective (kgSpatialSourceRecord a s Ω) := by
  intro r t h
  have hh : kgSpatialOriginalRay a r = kgSpatialOriginalRay a t :=
    kg_w9_standing_record_faithful a s Ω (kgOriginalObject a) h
  induction r using Quotient.inductionOn with
  | _ x =>
    induction t using Quotient.inductionOn with
    | _ y =>
      obtain ⟨c,hc,he⟩ := Quotient.exact hh
      apply Quotient.sound
      refine ⟨c,hc,(kgSpatialCoreOriginalEmbedding a).injective ?_⟩
      exact ((kgSpatialCoreOriginalEmbedding a).map_smul c x.val).trans he

theorem kg_spatial_complete_original_source_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (r : PhysicalRay (kgOriginalSpatialCore a)) :
    kgW9OriginalResponse a s Ω (kgSpatialOriginalRay a r) =
      (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
        (wickCommonRoleSourcePresentation a s Ω
          (kgOriginalQuantumToRay a (kgSpatialOriginalRay a r))))).val :=
  kg_w9_complete_original_source_square a s Ω (kgSpatialOriginalRay a r)

theorem kg_spatial_source_complete_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgSpatialSourceRecord a s Ω (rayMap _ x) q =
      kgFamilyOutput a s Ω (kgOriginalObject a)
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) x) q :=
  kg_w9_standing_complete_record a s Ω (kgOriginalObject a) _ q

theorem kg_spatial_first_failure_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (word : List (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    kgFirstFailure (kgSpatialSourceRecord a s Ω (rayMap _ x)) word =
      kgFirstFailure (kgFamilyOutput a s Ω (kgOriginalObject a)
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) x)) word := by
  apply congrArg (fun output => kgFirstFailure output word)
  funext q
  exact kg_spatial_source_complete_record a s Ω x q

theorem kg_spatial_regional_record (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V)
    (r : PhysicalRay (kgOriginalSpatialCore a))
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgSpatialSourceRecord a s V r (kgFamilyQuestionExtend h q) =
      kgSpatialSourceRecord a s Ω r q :=
  kg_standing_region_record a s h (kgOriginalObject a) (kgSpatialOriginalRay a r) q

theorem kg_spatial_original_weights (a : Parameters)
    (x y : PureVector (kgOriginalSpatialCore a)) :
    transitionProbability
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) x)
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) y) =
      transitionProbability x y := by
  have hi : inner ℂ ((kgSpatialCoreOriginalEmbedding a) x.val)
      ((kgSpatialCoreOriginalEmbedding a) y.val) = inner ℂ x.val y.val :=
    by simp [inner_eq_sum_norm_sq_div_four, ← (kgSpatialCoreOriginalEmbedding a).norm_map]
  simp only [transitionProbability,kgPureIsometryMap,
    (kgSpatialCoreOriginalEmbedding a).norm_map,hi]

def kgSpatialSourceReference (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (kgOriginalSpatialCore a))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :=
  (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).standingReferences.referenceAt
    (kgSpatialOriginalRay a r) q

theorem kg_spatial_reference_original_square (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    kgSpatialSourceReference a s Ω (rayMap _ x) q =
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.referenceAt
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) x) q :=
  (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).standing_reference_square _ q

theorem kg_spatial_scalar_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (c : ℂ) (hc : c ≠ 0) (x : PureVector (kgOriginalSpatialCore a))
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgSpatialSourceRecord a s Ω (rayMap _ (PureVector.smul c hc x)) q =
      kgSpatialSourceRecord a s Ω (rayMap _ x) q := by
  rw [kg_spatial_source_complete_record,kg_spatial_source_complete_record,
    kg_pure_isometry_scalar]
  exact kg_family_output_scalar a s Ω (kgOriginalObject a) c hc _ q

theorem kg_spatial_independent_product_weights (a : Parameters)
    (x y z w : PureVector (kgOriginalSpatialCore a)) :
    transitionProbability
      (kgRawTensor (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) x)
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) y))
      (kgRawTensor (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) z)
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) w)) =
      transitionProbability x z * transitionProbability y w := by
  rw [kg_raw_tensor_weights_multiply,kg_spatial_original_weights,
    kg_spatial_original_weights]

def kgOriginalOneCoreFlow (a : Parameters) (q : ProperPoincareTransform) :
    kgOriginalOneCore a ≃ₗᵢ[ℂ] kgOriginalOneCore a where
  toFun x := ⟨kgCorePoincareIsometry a q x.val,
    wick_original_poincare_preserves_isolated a q ⟨x.val.val,x.prop⟩⟩
  invFun x := ⟨kgCorePoincareIsometry a q⁻¹ x.val,
    wick_original_poincare_preserves_isolated a q⁻¹ ⟨x.val.val,x.prop⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change originalFockPoincareRepresentation a q⁻¹
      (originalFockPoincareRepresentation a q x.val.val) = x.val.val
    simpa only [map_inv] using
      (originalFockPoincareRepresentation a q).symm_apply_apply x.val.val
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change originalFockPoincareRepresentation a q
      (originalFockPoincareRepresentation a q⁻¹ x.val.val) = x.val.val
    simpa only [map_inv] using
      (originalFockPoincareRepresentation a q).apply_symm_apply x.val.val
  map_add' x y := Subtype.ext ((kgCorePoincareIsometry a q).map_add x.val y.val)
  map_smul' c x := Subtype.ext ((kgCorePoincareIsometry a q).map_smul c x.val)
  norm_map' x := (kgCorePoincareIsometry a q).norm_map x.val

def kgSpatialCoreOriginalFlow (a : Parameters) (q : ProperPoincareTransform) :
    kgOriginalSpatialCore a ≃ₗᵢ[ℂ] kgOriginalSpatialCore a :=
  (((kgOriginalSpatialCoreEquiv a).symm).trans (kgOriginalOneCoreFlow a q)).trans
    (kgOriginalSpatialCoreEquiv a)

theorem kg_spatial_original_flow_square (a : Parameters) (q : ProperPoincareTransform)
    (x : PureVector (kgOriginalSpatialCore a)) :
    kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a)
      (PureVector.mapUnitary (kgSpatialCoreOriginalFlow a q) x) =
      kgFamilyFlow q (A := kgOriginalObject a)
        (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) x) := by
  apply Subtype.ext
  change ((kgOriginalSpatialCoreEquiv a).symm
    (kgOriginalSpatialCoreEquiv a
      (kgOriginalOneCoreFlow a q ((kgOriginalSpatialCoreEquiv a).symm x.val)))).val = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem kg_spatial_original_continuation_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (q : ProperPoincareTransform)
    (x : PureVector (kgOriginalSpatialCore a))
    (test : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgSpatialSourceRecord a s Ω
      (rayMap _ (PureVector.mapUnitary (kgSpatialCoreOriginalFlow a q) x)) test =
      kgSpatialSourceRecord a s Ω (rayMap _ x) (kgFamilyFlowQuestion q test) := by
  rw [kg_spatial_source_complete_record,kg_spatial_source_complete_record,
    kg_spatial_original_flow_square]
  exact kg_family_flow_record a s Ω q (kgOriginalObject a) _ test

end AASCKleinGordon
