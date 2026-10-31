import KGNRSourceRecordTransport
import KGSpatialCompositionNaturality

/-! An explicit conservative NR receiving extension, not a silent claim that
the original Poincare protocol syntax was already closed under NR flow. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

abbrev KGNRReceivingQuestion (a : Parameters) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) := ℝ × KGFamilyQuestion a Ω ⟨A⟩

def kgNROldQuestion {a : Parameters} {Ω : Opens CoordinatePoint} {A : KGComparisonObject}
    (q : KGFamilyQuestion a Ω ⟨A⟩) : KGNRReceivingQuestion a Ω A := (0,q)

def kgNRReceivingOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : KGNRReceivingQuestion a Ω A) : KGFamilyReadout :=
  kgSpatialFamilyRecord a s Ω A
    (rayMap _ (PureVector.mapUnitary (kgNRSpatialFamilyFlow a q.1 A) x)) q.2

theorem kg_nr_receiving_old_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : KGFamilyQuestion a Ω ⟨A⟩) :
    kgNRReceivingOutput a s Ω A x (kgNROldQuestion q) =
      kgSpatialFamilyRecord a s Ω A (rayMap _ x) q := by
  unfold kgNRReceivingOutput kgNROldQuestion
  rw [kg_nr_spatial_family_pure_zero]

theorem kg_nr_receiving_scalar_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGNRReceivingQuestion a Ω A) :
    kgNRReceivingOutput a s Ω A (PureVector.smul c hc x) q =
      kgNRReceivingOutput a s Ω A x q := by
  have h : PureVector.mapUnitary (kgNRSpatialFamilyFlow a q.1 A) (PureVector.smul c hc x) =
      PureVector.smul c hc (PureVector.mapUnitary (kgNRSpatialFamilyFlow a q.1 A) x) :=
    Subtype.ext ((kgNRSpatialFamilyFlow a q.1 A).map_smul c x.val)
  unfold kgNRReceivingOutput
  rw [h,rayMap_smul]

theorem kg_nr_receiving_exact_old_standing (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x y : PureVector (KGSpatialFamilyCarrier a A)) :
    (∀ q,kgNRReceivingOutput a s Ω A x q = kgNRReceivingOutput a s Ω A y q) ↔
      rayMap _ x = rayMap _ y := by
  constructor
  · intro h
    apply kg_spatial_family_record_faithful a s Ω A
    funext q
    exact (kg_nr_receiving_old_record a s Ω A x q).symm.trans
      ((h (kgNROldQuestion q)).trans (kg_nr_receiving_old_record a s Ω A y q))
  · intro h q
    change kgSpatialFamilyRecord a s Ω A
      (unitaryRayMap (kgNRSpatialFamilyFlow a q.1 A) (rayMap _ x)) q.2 =
      kgSpatialFamilyRecord a s Ω A
        (unitaryRayMap (kgNRSpatialFamilyFlow a q.1 A) (rayMap _ y)) q.2
    rw [h]

def kgNRQuestionAdvance {a : Parameters} {Ω : Opens CoordinatePoint} {A : KGComparisonObject}
    (t : ℝ) (q : KGNRReceivingQuestion a Ω A) : KGNRReceivingQuestion a Ω A := (q.1+t,q.2)

theorem kg_nr_receiving_continuation_record (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGNRReceivingQuestion a Ω A) :
    kgNRReceivingOutput a s Ω A (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x) q =
      kgNRReceivingOutput a s Ω A x (kgNRQuestionAdvance t q) := by
  unfold kgNRReceivingOutput kgNRQuestionAdvance
  rw [kg_nr_spatial_family_pure_add]

theorem kg_nr_receiving_old_first_failure (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (word : List (KGFamilyQuestion a Ω ⟨A⟩)) :
    kgFirstFailure (kgNRReceivingOutput a s Ω A x) (word.map kgNROldQuestion) =
      kgFirstFailure (kgSpatialFamilyRecord a s Ω A (rayMap _ x)) word :=
  kg_first_failure_map _ _ _ (kg_nr_receiving_old_record a s Ω A x) word

def kgNRReceivingRegisteredOrbit (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGComparisonObject) :
    RawRegisteredOrbit (PureVector (KGSpatialFamilyCarrier a A)) (KGNRReceivingQuestion a Ω A)
      KGFamilyReadout (PhysicalRay (KGSpatialFamilyCarrier a A)) where
  output := kgNRReceivingOutput a s Ω A
  succeeds := kgFamilySuccess
  weight := transitionProbability
  outgoing y := kgNROldQuestion (.comparison (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) y))
  incoming y := kgNROldQuestion (.reverseComparison (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) y))
  probabilityValue := KGFamilyReadout.comparison
  probability_injective := by intro r t h;exact KGFamilyReadout.comparison.inj h
  outgoing_output x y := by
    rw [kg_nr_receiving_old_record,kg_spatial_family_complete_original_record]
    exact congrArg KGFamilyReadout.comparison
      (kg_pure_isometry_weight (kgSpatialFamilyOriginalEmbedding a A) x y)
  incoming_output x y := by
    rw [kg_nr_receiving_old_record,kg_spatial_family_complete_original_record]
    exact congrArg KGFamilyReadout.comparison
      (kg_pure_isometry_weight (kgSpatialFamilyOriginalEmbedding a A) y x)
  probability_success _ := rfl
  orbit := PureVector.ScalarRel
  phase_output x y h q := by
    obtain ⟨c,hc,h⟩ := h
    have he : PureVector.smul c hc x = y := Subtype.ext h
    rw [← he]
    exact (kg_nr_receiving_scalar_record a s Ω A c hc x q).symm
  raw_profiles_exact x y := (kg_raw_profiles_exact_orbits x y).trans
    (rayMap_eq_iff (KGSpatialFamilyCarrier a A) x y)
  q := rayMap _
  q_surjective r := by induction r using Quotient.inductionOn with | _ x => exact ⟨x,rfl⟩
  q_fibres := rayMap_eq_iff _
  coequalizer f hf := kg_raw_orbit_coequalizer f hf

theorem kg_nr_receiving_registered_standing_exact (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x y : PureVector (KGSpatialFamilyCarrier a A)) :
    (kgNRReceivingRegisteredOrbit a s Ω A).SameRegisteredStanding x y ↔
      rayMap _ x = rayMap _ y :=
  (kgNRReceivingRegisteredOrbit a s Ω A).registered_standing_exact x y

theorem kg_nr_receiving_same_original_registered_standing (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x y : PureVector (KGSpatialFamilyCarrier a A)) :
    (kgNRReceivingRegisteredOrbit a s Ω A).SameRegisteredStanding x y ↔
      (kgRawRegisteredOrbit a s Ω ⟨A⟩).SameRegisteredStanding
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x)
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) y) := by
  constructor
  · intro h
    apply (kg_registered_orbit_exact a s Ω ⟨A⟩ _ _).mpr
    exact congrArg (kgSpatialFamilyOriginalRay a A)
      ((kg_nr_receiving_registered_standing_exact a s Ω A x y).mp h)
  · intro h
    apply (kg_nr_receiving_registered_standing_exact a s Ω A x y).mpr
    exact kg_ray_isometry_injective (kgSpatialFamilyOriginalEmbedding a A)
      ((kg_registered_orbit_exact a s Ω ⟨A⟩ _ _).mp h)

theorem kg_nr_receiving_continuation_unique (a : Parameters) (t : ℝ)
    (A : KGComparisonObject) :
    ∃! C : PhysicalRay (KGSpatialFamilyCarrier a A) → PhysicalRay (KGSpatialFamilyCarrier a A),
      ∀ x,C (rayMap _ x) = rayMap _ (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x) := by
  refine ⟨unitaryRayMap (kgNRSpatialFamilyFlow a t A),by intro x;rfl,?_⟩
  intro C hc
  funext r
  induction r using Quotient.inductionOn with
  | _ x => exact hc x

theorem kg_nr_receiving_continuation_weights (a : Parameters) (t : ℝ)
    (A : KGComparisonObject) (x y : PureVector (KGSpatialFamilyCarrier a A)) :
    transitionProbability (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x)
      (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) y) = transitionProbability x y :=
  transitionProbability_mapUnitary _ x y

theorem kg_nr_receiving_old_registered_reference (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω ⟨A⟩)) :
    (kgNRReceivingRegisteredOrbit a s Ω A).references.referenceAt x
      (mapRegisteredQuestion kgNROldQuestion q) =
      (kgRawRegisteredOrbit a s Ω ⟨A⟩).references.referenceAt
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x) q :=
  reference_from_record_square (kgRawRegisteredOrbit a s Ω ⟨A⟩)
    (kgNRReceivingRegisteredOrbit a s Ω A)
    (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A) x) x
    kgNROldQuestion rfl (fun q =>
      (kg_nr_receiving_old_record a s Ω A x q).trans
        (kg_spatial_family_complete_original_record a s Ω A x q)) q

theorem kg_nr_receiving_continuation_reference (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGNRReceivingQuestion a Ω A)) :
    (kgNRReceivingRegisteredOrbit a s Ω A).references.referenceAt x
      (mapRegisteredQuestion (kgNRQuestionAdvance t) q) =
      (kgNRReceivingRegisteredOrbit a s Ω A).references.referenceAt
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x) q :=
  reference_from_record_square (kgNRReceivingRegisteredOrbit a s Ω A)
    (kgNRReceivingRegisteredOrbit a s Ω A)
    (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x) x
    (kgNRQuestionAdvance t) rfl
    (fun q => (kg_nr_receiving_continuation_record a s t Ω A x q).symm) q

theorem kg_nr_receiving_continuation_first_failure (a : Parameters) (s t : ℝ)
    (Ω : Opens CoordinatePoint) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (word : List (KGNRReceivingQuestion a Ω A)) :
    kgFirstFailure (kgNRReceivingOutput a s Ω A x) (word.map (kgNRQuestionAdvance t)) =
      kgFirstFailure (kgNRReceivingOutput a s Ω A
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A) x)) word :=
  kg_first_failure_map _ _ _
    (fun q => (kg_nr_receiving_continuation_record a s t Ω A x q).symm) word

def kgNRQuestionExtend {a : Parameters} {Ω V : Opens CoordinatePoint}
    {A : KGComparisonObject} (h : Ω ≤ V) (q : KGNRReceivingQuestion a Ω A) :
    KGNRReceivingQuestion a V A := (q.1,kgFamilyQuestionExtend h q.2)

theorem kg_nr_receiving_regional_record (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGNRReceivingQuestion a Ω A) :
    kgNRReceivingOutput a s V A x (kgNRQuestionExtend h q) =
      kgNRReceivingOutput a s Ω A x q :=
  kg_spatial_family_regional_record a s h A _ q.2

theorem kg_nr_receiving_regional_reference (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGComparisonObject)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGNRReceivingQuestion a Ω A)) :
    (kgNRReceivingRegisteredOrbit a s V A).references.referenceAt x
      (mapRegisteredQuestion (kgNRQuestionExtend h) q) =
      (kgNRReceivingRegisteredOrbit a s Ω A).references.referenceAt x q :=
  reference_from_record_square (kgNRReceivingRegisteredOrbit a s Ω A)
    (kgNRReceivingRegisteredOrbit a s V A) x x (kgNRQuestionExtend h) rfl
    (kg_nr_receiving_regional_record a s h A x) q

def KGNRLiftCompatible {a : Parameters} {A B : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) : Prop :=
  ∀ (t : ℝ) x,f.spatial (kgNRSpatialFamilyFlow a t A x) =
    kgNRSpatialFamilyFlow a t B (f.spatial x)

theorem kg_nr_associator_lift_compatible (a : Parameters) (A B C : KGComparisonObject) :
    KGNRLiftCompatible (kgSpatialAssociatorLift a A B C) := by
  intro t x
  have he : (TensorProduct.assoc ℂ (KGSpatialFamilyCarrier a A)
      (KGSpatialFamilyCarrier a B) (KGSpatialFamilyCarrier a C)).toLinearMap.comp
      (kgNRSpatialFamilyFlow a t (.tensor (.tensor A B) C)).toLinearMap =
      (kgNRSpatialFamilyFlow a t (.tensor A (.tensor B C))).toLinearMap.comp
        (TensorProduct.assoc ℂ _ _ _).toLinearMap := by
    apply TensorProduct.ext_threefold
    intro x y z
    rfl
  exact LinearMap.congr_fun he x

theorem kg_nr_symmetry_lift_compatible (a : Parameters) (A B : KGComparisonObject) :
    KGNRLiftCompatible (kgSpatialSymmetryLift a A B) := by
  intro t x
  have he : (TensorProduct.comm ℂ (KGSpatialFamilyCarrier a A)
      (KGSpatialFamilyCarrier a B)).toLinearMap.comp
      (kgNRSpatialFamilyFlow a t (.tensor A B)).toLinearMap =
      (kgNRSpatialFamilyFlow a t (.tensor B A)).toLinearMap.comp
        (TensorProduct.comm ℂ _ _).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  exact LinearMap.congr_fun he x

theorem kg_nr_left_unitor_lift_compatible (a : Parameters) (A : KGComparisonObject) :
    KGNRLiftCompatible (kgSpatialLeftUnitorLift a A) := by
  intro t x
  have he : (TensorProduct.lid ℂ (KGSpatialFamilyCarrier a A)).toLinearMap.comp
      (kgNRSpatialFamilyFlow a t (.tensor .unit A)).toLinearMap =
      (kgNRSpatialFamilyFlow a t A).toLinearMap.comp (TensorProduct.lid ℂ _).toLinearMap := by
    apply TensorProduct.ext'
    intro c x
    exact ((kgNRSpatialFamilyFlow a t A).map_smul c x).symm
  exact LinearMap.congr_fun he x

theorem kg_nr_right_unitor_lift_compatible (a : Parameters) (A : KGComparisonObject) :
    KGNRLiftCompatible (kgSpatialRightUnitorLift a A) := by
  intro t x
  have hs := kg_nr_symmetry_lift_compatible a A .unit t x
  have hl := kg_nr_left_unitor_lift_compatible a A t
    ((kgSpatialSymmetryLift a A .unit).spatial x)
  exact (congrArg (kgSpatialLeftUnitorLift a A).spatial hs).trans hl

theorem kg_nr_identity_lift_compatible (a : Parameters) (A : KGComparisonObject) :
    KGNRLiftCompatible (kgSpatialIdentityLift a A) := by intro t x;rfl

theorem kg_nr_compose_lift_compatible {a : Parameters} {A B C : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) (g : KGSpatialComparisonLift a B C)
    (hf : KGNRLiftCompatible f) (hg : KGNRLiftCompatible g) :
    KGNRLiftCompatible (kgSpatialComposeLift f g) := by
  intro t x
  change g.spatial (f.spatial (kgNRSpatialFamilyFlow a t A x)) =
    kgNRSpatialFamilyFlow a t C (g.spatial (f.spatial x))
  rw [hf t x,hg t (f.spatial x)]

theorem kg_nr_tensor_lift_compatible {a : Parameters} {A B C D : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) (g : KGSpatialComparisonLift a C D)
    (hf : KGNRLiftCompatible f) (hg : KGNRLiftCompatible g) :
    KGNRLiftCompatible (kgSpatialTensorLift f g) := by
  intro t x
  have he : (TensorProduct.congr f.spatial.toLinearEquiv g.spatial.toLinearEquiv).toLinearMap.comp
      (kgNRSpatialFamilyFlow a t (.tensor A C)).toLinearMap =
      (kgNRSpatialFamilyFlow a t (.tensor B D)).toLinearMap.comp
        (TensorProduct.congr f.spatial.toLinearEquiv g.spatial.toLinearEquiv).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    change f.spatial (kgNRSpatialFamilyFlow a t A x) ⊗ₜ[ℂ]
      g.spatial (kgNRSpatialFamilyFlow a t C y) =
      kgNRSpatialFamilyFlow a t B (f.spatial x) ⊗ₜ[ℂ]
        kgNRSpatialFamilyFlow a t D (g.spatial y)
    rw [hf t x,hg t y]
  exact LinearMap.congr_fun he x

def kgSpatialInverseLift {a : Parameters} {A B : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) : KGSpatialComparisonLift a B A where
  original := kgInternalInverse f.original
  spatial := f.spatial.symm
  vector_square x := by
    have h := congrArg f.original.isometry.symm (f.vector_square (f.spatial.symm x))
    rw [f.spatial.apply_symm_apply,f.original.isometry.symm_apply_apply] at h
    exact h.symm

theorem kg_nr_inverse_lift_compatible {a : Parameters} {A B : KGComparisonObject}
    (f : KGSpatialComparisonLift a A B) (hf : KGNRLiftCompatible f) :
    KGNRLiftCompatible (kgSpatialInverseLift f) := by
  intro t x
  apply f.spatial.injective
  have h := hf t (f.spatial.symm x)
  simpa only [kgSpatialInverseLift,LinearIsometryEquiv.apply_symm_apply] using h.symm

theorem kg_nr_receiving_tensor_standing {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A B : KGComparisonObject) (x x' : PureVector (KGSpatialFamilyCarrier a A))
    (y y' : PureVector (KGSpatialFamilyCarrier a B))
    (hx : (kgNRReceivingRegisteredOrbit a s Ω A).SameRegisteredStanding x x')
    (hy : (kgNRReceivingRegisteredOrbit a s Ω B).SameRegisteredStanding y y') :
    (kgNRReceivingRegisteredOrbit a s Ω (.tensor A B)).SameRegisteredStanding
      (kgRawTensor x y) (kgRawTensor x' y') := by
  apply (kg_nr_receiving_registered_standing_exact a s Ω (.tensor A B) _ _).mpr
  exact congrArg₂ kgTensorRay
    ((kg_nr_receiving_registered_standing_exact a s Ω A x x').mp hx)
    ((kg_nr_receiving_registered_standing_exact a s Ω B y y').mp hy)

def kgNRQuestionPullback {a : Parameters} {Ω : Opens CoordinatePoint}
    {A B : KGComparisonObject} (f : KGSpatialComparisonLift a A B)
    (q : KGNRReceivingQuestion a Ω B) : KGNRReceivingQuestion a Ω A :=
  (q.1,kgFamilyQuestionPullback f.original q.2)

theorem kg_nr_receiving_comparison_record (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (f : KGSpatialComparisonLift a A B) (compatible : KGNRLiftCompatible f)
    (x : PureVector (KGSpatialFamilyCarrier a A)) (q : KGNRReceivingQuestion a Ω B) :
    kgNRReceivingOutput a s Ω B (PureVector.mapUnitary f.spatial x) q =
      kgNRReceivingOutput a s Ω A x (kgNRQuestionPullback f q) := by
  have he : PureVector.mapUnitary (kgNRSpatialFamilyFlow a q.1 B)
      (PureVector.mapUnitary f.spatial x) =
      PureVector.mapUnitary f.spatial (PureVector.mapUnitary (kgNRSpatialFamilyFlow a q.1 A) x) :=
    Subtype.ext (compatible q.1 x.val).symm
  unfold kgNRReceivingOutput kgNRQuestionPullback
  rw [he]
  exact kg_spatial_comparison_lift_complete_record a s Ω A B f _ q.2

theorem kg_nr_receiving_comparison_reference (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (A B : KGComparisonObject)
    (f : KGSpatialComparisonLift a A B) (compatible : KGNRLiftCompatible f)
    (x : PureVector (KGSpatialFamilyCarrier a A))
    (q : RegisteredQuestion (KGNRReceivingQuestion a Ω B)) :
    (kgNRReceivingRegisteredOrbit a s Ω A).references.referenceAt x
      (mapRegisteredQuestion (kgNRQuestionPullback f) q) =
      (kgNRReceivingRegisteredOrbit a s Ω B).references.referenceAt
        (PureVector.mapUnitary f.spatial x) q :=
  reference_from_record_square (kgNRReceivingRegisteredOrbit a s Ω B)
    (kgNRReceivingRegisteredOrbit a s Ω A) (PureVector.mapUnitary f.spatial x) x
    (kgNRQuestionPullback f) rfl
    (fun q => (kg_nr_receiving_comparison_record a s Ω A B f compatible x q).symm) q

end AASCKleinGordon
