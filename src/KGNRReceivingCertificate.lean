import KGNRReceivingBase

/-! Invoked time regularity and the source-certified receiving assembly.
Original lawfulness remains the original execution/reference/failure relation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion Filter
open scoped TensorProduct Topology
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

theorem kg_nr_family_time_continuous (a : Parameters) (A : KGComparisonObject)
    (x : KGSpatialFamilyCarrier a A) : Continuous (fun t => kgNRSpatialFamilyFlow a t A x) := by
  induction A with
  | unit => exact continuous_const
  | kg => exact kg_nr_source_core_flow_continuous a x
  | tensor A B hA hB =>
    induction x using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : KGSpatialFamilyCarrier a (.tensor A B))))
    | tmul x y =>
      change Continuous (fun t => kgTensorCLM (E := KGSpatialFamilyCarrier a A)
        (F := KGSpatialFamilyCarrier a B) (kgNRSpatialFamilyFlow a t A x) (kgNRSpatialFamilyFlow a t B y))
      exact ((kgTensorCLM (E := KGSpatialFamilyCarrier a A)
        (F := KGSpatialFamilyCarrier a B)).continuous.comp (hA x)).clm_apply (hB y)
    | add x y hx hy => simpa only [map_add] using hx.add hy

section JointTime
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem kg_joint_isometric_action_continuous (U : ℝ → E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x,Continuous (fun t => U t x)) : Continuous (fun p : ℝ × E => U p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hz : Tendsto (fun q : ℝ × E => U q.1 (q.2-p.2)) (nhds p) (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [LinearIsometryEquiv.norm_map,sub_self,norm_zero] using
      ((continuous_snd.sub continuous_const).norm.continuousAt.tendsto :
        Tendsto (fun q : ℝ × E => ‖q.2-p.2‖) (nhds p) (nhds ‖p.2-p.2‖))
  have ht : Tendsto (fun q : ℝ × E => U q.1 p.2) (nhds p) (nhds (U p.1 p.2)) :=
    (hU p.2).continuousAt.tendsto.comp continuous_fst.continuousAt.tendsto
  have hs := hz.add ht
  simpa only [map_sub,sub_add_cancel,zero_add] using hs

theorem kg_joint_pure_isometric_action_continuous (U : ℝ → E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x,Continuous (fun t => U t x)) :
    Continuous (fun p : ℝ × PureVector E => PureVector.mapUnitary (U p.1) p.2) :=
  ((kg_joint_isometric_action_continuous U hU).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem kg_joint_ray_isometric_action_continuous (U : ℝ → E ≃ₗᵢ[ℂ] E)
    (hU : ∀ x,Continuous (fun t => U t x)) :
    Continuous (fun p : ℝ × PhysicalRay E => unitaryRayMap (U p.1) p.2) := by
  have hi : IsOpenQuotientMap (id : ℝ → ℝ) :=
    ⟨Function.surjective_id,continuous_id,fun _ h => by simpa using h⟩
  apply (hi.prodMap (kg_ray_open_quotient (E := E))).continuous_comp_iff.mp
  exact kg_raw_orbit_map_continuous.comp (kg_joint_pure_isometric_action_continuous U hU)
end JointTime

theorem kg_nr_receiving_joint_time_regular (a : Parameters) (A : KGNRObject a) :
    Continuous (fun p : ℝ × PhysicalRay (KGNRCarrier A) =>
      unitaryRayMap (kgNRSpatialFamilyFlow a p.1 A.shape) p.2) :=
  kg_joint_ray_isometric_action_continuous _ (kg_nr_family_time_continuous a A.shape)

theorem kg_nr_full_spatial_time_continuous (a : Parameters) (x : KGNRSpatialHilbert) :
    Continuous (fun t => kgNRSpatialFreeFlow a t x) :=
  (kgPhysicalSpatialUnitary a).continuous.comp
    (kg_nr_free_momentum_flow_continuous a ((kgPhysicalSpatialUnitary a).symm x))

def kgNRParticleCore (a : Parameters) : kgOriginalOneCore a :=
  ⟨(kgFamilyParticle a).val,wick_isolated_one_particle_contains_original_core a oneParticleSector⟩

def kgNRParticleSpatial (a : Parameters) : PureVector (kgOriginalSpatialCore a) :=
  ⟨kgOriginalSpatialCoreEquiv a (kgNRParticleCore a),by
    intro h
    have hz : kgNRParticleCore a = 0 :=
      (kgOriginalSpatialCoreEquiv a).injective
        (h.trans (kgOriginalSpatialCoreEquiv a).map_zero.symm)
    exact (kgFamilyParticle a).prop (congrArg Subtype.val hz)⟩

theorem kg_nr_particle_original_square (a : Parameters) :
    kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a .kg) (kgNRParticleSpatial a) =
      kgFamilyParticle a := by
  apply Subtype.ext
  change ((kgOriginalSpatialCoreEquiv a).symm
    (kgOriginalSpatialCoreEquiv a (kgNRParticleCore a))).val = _
  exact congrArg Subtype.val ((kgOriginalSpatialCoreEquiv a).symm_apply_apply (kgNRParticleCore a))

def kgNRFamilyPreparation (a : Parameters) :
    (A : KGComparisonObject) → PureVector (KGSpatialFamilyCarrier a A)
  | .unit => show PureVector ℂ from ⟨(1 : ℂ),one_ne_zero⟩
  | .kg => kgNRParticleSpatial a
  | .tensor A B => kgRawTensor (kgNRFamilyPreparation a A) (kgNRFamilyPreparation a B)

def kgNRFailureQuestion (a : Parameters) (Ω : Opens CoordinatePoint) :
    KGFamilyQuestion a Ω ⟨.tensor .kg .kg⟩ :=
  .original (.right .original (kgFamilyVacuum a).val)
    (.original (.comparison 1 ⟨vacuumCore,vacuumCore_nonzero⟩))

theorem kg_nr_receiving_actual_failure (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    (kgNRReceivingRegisteredOrbit a s Ω (.tensor .kg .kg)).kernel.FailureAt
      (kgNRFamilyPreparation a (.tensor .kg .kg)) (.execution (kgNROldQuestion (kgNRFailureQuestion a Ω))) := by
  apply ((kgNRReceivingRegisteredOrbit a s Ω (.tensor .kg .kg)).execution_failure_iff _ _).mpr
  change ¬ kgFamilySuccess (kgNRReceivingOutput a s Ω (.tensor .kg .kg) _ _)
  rw [kg_nr_receiving_old_record,kg_spatial_family_complete_original_record]
  have hs : kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a (.tensor .kg .kg))
      (kgNRFamilyPreparation a (.tensor .kg .kg)) =
      kgRawTensor (kgFamilyParticle a) (kgFamilyParticle a) := by
    rw [kgNRFamilyPreparation,kg_spatial_family_tensor_original_square]
    change kgRawTensor (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a .kg) (kgNRParticleSpatial a))
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a .kg) (kgNRParticleSpatial a)) = _
    rw [kg_nr_particle_original_square]
  rw [hs]
  have hz : kgExtractionMap (a := a)
      (A := kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))
      (.right (.original : KGExtraction a (kgOriginalObject a)) (kgFamilyVacuum a).val)
      (kgRawTensor (kgFamilyParticle a) (kgFamilyParticle a)).val = 0 := by
    rw [kg_extraction_right_product,kg_family_vacuum_particle_inner,zero_smul]
  rw [show kgFamilyOutput a s Ω ⟨.tensor .kg .kg⟩
      (kgRawTensor (kgFamilyParticle a) (kgFamilyParticle a)) (kgNRFailureQuestion a Ω) =
      .extraction none from kg_family_zero_extraction s Ω _ _ _ hz]
  change ¬ some KGExecutionFailure.zeroExtraction = none
  exact Option.some_ne_none _

structure KGNRReceivingQS (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Prop where
  upstream : KGSpecificStandingSource a s Ω
  nonempty : ∀ A : KGNRObject a,Nonempty (PureVector (KGNRCarrier A))
  actual_failure : (kgNRReceivingRegisteredOrbit a s Ω (.tensor .kg .kg)).kernel.Nontrivial
  irreversible : AASC.Asymmetric
    (kgNRReceivingRegisteredOrbit a s Ω (.tensor .kg .kg)).kernel.StandingToFailure
  old_complete_records : ∀ (A : KGNRObject a) (x : PureVector (KGNRCarrier A))
    (q : KGFamilyQuestion a Ω A.raw),
    kgNRReceivingOutput a s Ω A.shape x (kgNROldQuestion q) =
      kgFamilyOutput a s Ω A.raw (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A.shape) x) q
  standing : ∀ (A : KGNRObject a) (x y : PureVector (KGNRCarrier A)),
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).SameRegisteredStanding x y ↔ rayMap _ x = rayMap _ y
  realized_identity : ∀ (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A),
    kgNRRealizedPullback a s Ω (𝟙 A) q = q
  realized_composition : ∀ {A B C : KGNRObject a} (f : A ⟶ B) (g : B ⟶ C)
    (q : KGNRRealizedQuestion a s Ω C),kgNRRealizedPullback a s Ω (f ≫ g) q =
      kgNRRealizedPullback a s Ω f (kgNRRealizedPullback a s Ω g q)
  orbit_open : ∀ A : KGNRObject a,IsOpenQuotientMap (rayMap (KGNRCarrier A))
  time_regular : ∀ A : KGNRObject a,Continuous (fun p : ℝ × PhysicalRay (KGNRCarrier A) =>
    unitaryRayMap (kgNRSpatialFamilyFlow a p.1 A.shape) p.2)
  tensor_regular : ∀ A B : KGNRObject a,Continuous
    (fun p : PhysicalRay (KGNRCarrier A) × PhysicalRay (KGNRCarrier B) => kgTensorRay p.1 p.2)
  comparison_symmetric : Nonempty (SymmetricCategory (KGNRObject a))
  old_references : ∀ (A : KGNRObject a) (x : PureVector (KGNRCarrier A))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω A.raw)),
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt x
      (mapRegisteredQuestion kgNROldQuestion q) =
      (kgRawRegisteredOrbit a s Ω A.raw).references.referenceAt
        (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A.shape) x) q
  comparison_references : ∀ {A B : KGNRObject a} (f : A ⟶ B)
    (x : PureVector (KGNRCarrier A)) (q : RegisteredQuestion (KGNRReceivingQuestion a Ω B.shape)),
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt x
      (mapRegisteredQuestion (kgNRQuestionPullback f.lift) q) =
    (kgNRReceivingRegisteredOrbit a s Ω B.shape).references.referenceAt
      (PureVector.mapUnitary f.lift.spatial x) q
  regional_references : ∀ (V : Opens CoordinatePoint) (h : Ω ≤ V) (A : KGNRObject a)
    (x : PureVector (KGNRCarrier A)) (q : RegisteredQuestion (KGNRReceivingQuestion a Ω A.shape)),
    (kgNRReceivingRegisteredOrbit a s V A.shape).references.referenceAt x
      (mapRegisteredQuestion (kgNRQuestionExtend h) q) =
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt x q
  continuation_references : ∀ (A : KGNRObject a) (t : ℝ) (x : PureVector (KGNRCarrier A))
    (q : RegisteredQuestion (KGNRReceivingQuestion a Ω A.shape)),
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt x
      (mapRegisteredQuestion (kgNRQuestionAdvance t) q) =
    (kgNRReceivingRegisteredOrbit a s Ω A.shape).references.referenceAt
      (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x) q
  realized_region_identity : ∀ (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A),
    kgNRRealizedRegion a s (le_refl Ω) A q = q
  realized_region_composition : ∀ (V W : Opens CoordinatePoint) (h : Ω ≤ V) (k : V ≤ W)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A),
    kgNRRealizedRegion a s (le_trans h k) A q =
      kgNRRealizedRegion a s k A (kgNRRealizedRegion a s h A q)
  realized_region_arrow : ∀ (V : Opens CoordinatePoint) (h : Ω ≤ V) {A B : KGNRObject a}
    (f : A ⟶ B) (q : KGNRRealizedQuestion a s Ω B),
    kgNRRealizedRegion a s h A (kgNRRealizedPullback a s Ω f q) =
      kgNRRealizedPullback a s V f (kgNRRealizedRegion a s h B q)
  realized_region_time : ∀ (V : Opens CoordinatePoint) (h : Ω ≤ V) (t : ℝ)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A),
    kgNRRealizedRegion a s h A (kgNRRealizedFlow a s Ω t A q) =
      kgNRRealizedFlow a s V t A (kgNRRealizedRegion a s h A q)
  realized_time_identity : ∀ (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A),
    kgNRRealizedFlow a s Ω 0 A q = q
  realized_time_composition : ∀ (t u : ℝ) (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A),
    kgNRRealizedFlow a s Ω (t+u) A q = kgNRRealizedFlow a s Ω u A (kgNRRealizedFlow a s Ω t A q)
  realized_time_arrow : ∀ (t : ℝ) {A B : KGNRObject a} (f : A ⟶ B)
    (q : KGNRRealizedQuestion a s Ω B),
    kgNRRealizedPullback a s Ω f (kgNRRealizedFlow a s Ω t B q) =
      kgNRRealizedFlow a s Ω t A (kgNRRealizedPullback a s Ω f q)
  continuation_tensor : ∀ (t : ℝ) (A B : KGNRObject a)
    (x : PureVector (KGNRCarrier A)) (y : PureVector (KGNRCarrier B)),
    PureVector.mapUnitary (kgNRSpatialFamilyFlow a t (.tensor A.shape B.shape)) (kgRawTensor x y) =
      kgRawTensor (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x)
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t B.shape) y)
  full_standing : ∀ (A : KGNRObject a) (x y : PureVector (KGNRCarrier A)),
    (kgRawRegisteredOrbit a s Ω A.raw).SameRegisteredStanding
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A.shape) x)
      (kgPureIsometryMap (kgSpatialFamilyOriginalEmbedding a A.shape) y) ↔
      kgNRFullProjection a A.shape (rayMap _ x) = kgNRFullProjection a A.shape (rayMap _ y)
  full_weights : ∀ (A : KGNRObject a) (x y : PureVector (KGNRCarrier A)),
    transitionProbability (kgPureIsometryMap (kgNRFullFamilyEmbedding a A.shape) x)
      (kgPureIsometryMap (kgNRFullFamilyEmbedding a A.shape) y) = transitionProbability x y
  full_tensor : ∀ (A B : KGNRObject a) (x : PureVector (KGNRCarrier A)) (y : PureVector (KGNRCarrier B)),
    kgPureIsometryMap (kgNRFullFamilyEmbedding a (.tensor A.shape B.shape)) (kgRawTensor x y) =
      kgRawTensor (kgPureIsometryMap (kgNRFullFamilyEmbedding a A.shape) x)
        (kgPureIsometryMap (kgNRFullFamilyEmbedding a B.shape) y)
  continuation_weights : ∀ (A : KGNRObject a) (t : ℝ) (x y : PureVector (KGNRCarrier A)),
    transitionProbability (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x)
      (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) y) = transitionProbability x y
  continuation_unique : ∀ (A : KGNRObject a) (t : ℝ),
    ∃! C : PhysicalRay (KGNRCarrier A) → PhysicalRay (KGNRCarrier A),
      ∀ x,C (rayMap _ x) = rayMap _ (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x)
  full_projection : ∀ A : KGNRObject a,Function.Injective (kgNRFullProjection a A.shape)
  full_projection_continuation : ∀ (A : KGNRObject a) (t : ℝ) (x : PureVector (KGNRCarrier A)),
    kgNRFullProjection a A.shape (unitaryRayMap (kgNRSpatialFamilyFlow a t A.shape) (rayMap _ x)) =
      unitaryRayMap (kgNRFullFamilyFlow a t A.shape) (kgNRFullProjection a A.shape (rayMap _ x))
  independent_weights : ∀ (A B : KGNRObject a) (x x' : PhysicalRay (KGNRCarrier A))
    (y y' : PhysicalRay (KGNRCarrier B)),
    rayTransitionProbability (kgTensorRay x y) (kgTensorRay x' y') =
      rayTransitionProbability x x' * rayTransitionProbability y y'
  first_failure : ∀ (A : KGNRObject a) (t : ℝ) (x : PureVector (KGNRCarrier A))
    (word : List (KGNRReceivingQuestion a Ω A.shape)),
    kgFirstFailure (kgNRReceivingOutput a s Ω A.shape x) (word.map (kgNRQuestionAdvance t)) =
      kgFirstFailure (kgNRReceivingOutput a s Ω A.shape
        (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x)) word

theorem kg_nr_receiving_qs_constructed (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGNRReceivingQS a s Ω where
  upstream := kg_constraint_first_standing_source a s Ω
  nonempty A := ⟨kgNRFamilyPreparation a A.shape⟩
  actual_failure := (RawRegisteredOrbit.objecthood_of_execution_failure _ _ _
    (kg_nr_receiving_actual_failure a s Ω)).2.2.2.1
  irreversible := (RawRegisteredOrbit.objecthood_of_execution_failure _ _ _
    (kg_nr_receiving_actual_failure a s Ω)).2.2.2.2
  old_complete_records A x q := (kg_nr_receiving_old_record a s Ω A.shape x q).trans
    (kg_spatial_family_complete_original_record a s Ω A.shape x q)
  standing A := kg_nr_receiving_registered_standing_exact a s Ω A.shape
  realized_identity := kg_nr_realized_identity a s Ω
  realized_composition := kg_nr_realized_composition a s Ω
  orbit_open := kg_nr_receiving_orbit_open a
  time_regular := kg_nr_receiving_joint_time_regular a
  tensor_regular := kg_nr_receiving_tensor_regular a
  comparison_symmetric := ⟨inferInstance⟩
  old_references A := kg_nr_receiving_old_registered_reference a s Ω A.shape
  comparison_references f := kg_nr_receiving_comparison_reference a s Ω _ _ f.lift f.compatible
  regional_references _V h A := kg_nr_receiving_regional_reference a s h A.shape
  continuation_references A t := kg_nr_receiving_continuation_reference a s t Ω A.shape
  realized_region_identity := kg_nr_realized_region_identity a s Ω
  realized_region_composition _V _W h k := kg_nr_realized_region_composition a s h k
  realized_region_arrow _V h := kg_nr_realized_region_arrow a s h
  realized_region_time _V h t := kg_nr_realized_region_flow a s t h
  realized_time_identity := kg_nr_realized_flow_zero a s Ω
  realized_time_composition t u := kg_nr_realized_flow_add a s t u Ω
  realized_time_arrow t := kg_nr_realized_flow_arrow a s Ω t
  continuation_tensor t A B := kg_nr_spatial_family_flow_tensor a t A.shape B.shape
  full_standing A := kg_nr_full_projection_original_standing a s Ω A.shape
  full_weights A := kg_nr_full_projection_weights a A.shape
  full_tensor A B := kg_nr_full_projection_tensor a A.shape B.shape
  continuation_weights A t := kg_nr_receiving_continuation_weights a t A.shape
  continuation_unique A t := kg_nr_receiving_continuation_unique a t A.shape
  full_projection A := kg_nr_full_projection_faithful a A.shape
  full_projection_continuation A t := kg_nr_full_projection_ray_continuation a t A.shape
  independent_weights _ _ := kg_tensor_ray_weights
  first_failure A t := kg_nr_receiving_continuation_first_failure a s t Ω A.shape

end AASCKleinGordon
