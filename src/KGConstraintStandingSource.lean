import KGFrameRecordFunctor
import KGFamilyNondegeneracy
import KGIndependentProductRecords
import KGTensorQuotientTopology

/-! A derived, instance-specific source bundle. Its fields are discharged below
from the constructed KG family. It is never an input to raw construction and is
not the generic QClose theorem for all possible corpus realizations. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgRegisteredWeight {a : Parameters} (A : KGFamilyObject a)
    (x y : PureVector (KGFamilyCarrier A)) : Set.Icc (0 : ℝ) 1 :=
  ⟨transitionProbability x y,kg_raw_probability_interval x y⟩

def kgStandingWeight {a : Parameters} (A : KGFamilyObject a)
    (r t : PhysicalRay (KGFamilyCarrier A)) : Set.Icc (0 : ℝ) 1 := by
  refine ⟨rayTransitionProbability r t,?_⟩
  induction r using Quotient.inductionOn with
  | _ x =>
    induction t using Quotient.inductionOn with
    | _ y => exact kg_raw_probability_interval x y

/-- The six raw coordinates for the fixed constructed family. This is an output
of the actual construction below, not a supplied bridge or same-I premise. -/
structure KGSpecificRawQP (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Prop where
  nonempty : ∀ A : KGFamilyObject a,Nonempty (PureVector (KGFamilyCarrier A))
  determinate : ∀ A : KGFamilyObject a,(kgRawRegisteredOrbit a s Ω A).references.incidenceSystem.Determinate
  actual_failure : (kgRawRegisteredOrbit a s Ω
    (kgFamilyTensor (kgOriginalObject a) (kgOriginalObject a))).kernel.Nontrivial
  interval : ∀ (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)),
    0 ≤ transitionProbability x y ∧ transitionProbability x y ≤ 1
  registered : ∀ (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)),
    (kgRawRegisteredOrbit a s Ω A).kernel.standing x
      (.execution (.comparison y)) (.comparison (transitionProbability x y))
  arrow_references : ∀ {A B : KGFamilyObject a} (f : A ⟶ B) (x : PureVector (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω B)),
    (kgRawRegisteredOrbit a s Ω A).references.referenceAt x
      (mapRegisteredQuestion (kgFamilyQuestionPullback f) π)=
      (kgRawRegisteredOrbit a s Ω B).references.referenceAt (PureVector.mapUnitary f.isometry x) π
  base_references : ∀ (V : Opens CoordinatePoint) (h : Ω ≤ V) (A : KGFamilyObject a)
    (x : PureVector (KGFamilyCarrier A)) (π : RegisteredQuestion (KGFamilyQuestion a Ω A)),
    (kgRawRegisteredOrbit a s V A).references.referenceAt x
      (mapRegisteredQuestion (kgFamilyQuestionExtend h) π)=
      (kgRawRegisteredOrbit a s Ω A).references.referenceAt x π
  scalar_one : ∀ (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)),kgRawScalarAction.smul (1 : ℂˣ) x=x
  scalar_mul : ∀ (A : KGFamilyObject a) (c d : ℂˣ) (x : PureVector (KGFamilyCarrier A)),
    kgRawScalarAction.smul (c*d) x=kgRawScalarAction.smul c (kgRawScalarAction.smul d x)
  scalar_weight : ∀ (A : KGFamilyObject a) (c d : ℂˣ) (x y : PureVector (KGFamilyCarrier A)),
    transitionProbability (kgRawScalarAction.smul c x) (kgRawScalarAction.smul d y)=transitionProbability x y
  scalar_record : ∀ (A : KGFamilyObject a) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A),
    kgFamilyOutput a s Ω A (PureVector.smul c hc x) π=kgFamilyOutput a s Ω A x π
  orbit_coequalizer : ∀ (A : KGFamilyObject a) (Y : Type) (f : PureVector (KGFamilyCarrier A) → Y),
    (∀ x y,PureVector.ScalarRel x y → f x=f y) →
      ∃! g : PhysicalRay (KGFamilyCarrier A) → Y,∀ x,g (rayMap _ x)=f x
  open_orbit_quotient : ∀ A : KGFamilyObject a,IsOpenQuotientMap (rayMap (KGFamilyCarrier A))
  continuous_orbit_coequalizer : ∀ (A : KGFamilyObject a) (Y : Type) [TopologicalSpace Y]
    (f : PureVector (KGFamilyCarrier A) → Y),Continuous f →
    (∀ x y,PureVector.ScalarRel x y → f x=f y) →
      ∃! g : PhysicalRay (KGFamilyCarrier A) → Y,Continuous g ∧ ∀ x,g (rayMap _ x)=f x
  raw_profile_complete : ∀ (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)),
    ((∀ z,transitionProbability x z=transitionProbability y z) ∧
      (∀ z,transitionProbability z x=transitionProbability z y)) ↔ rayMap _ x=rayMap _ y
  independent_scalar : ∀ (A B : KGFamilyObject a) (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (x : PureVector (KGFamilyCarrier A)) (y : PureVector (KGFamilyCarrier B)),
    kgRawTensor (PureVector.smul c hc x) (PureVector.smul d hd y)=
      PureVector.smul (c*d) (mul_ne_zero hc hd) (kgRawTensor x y)
  independent_weights : ∀ (A B : KGFamilyObject a)
    (x z : PureVector (KGFamilyCarrier A)) (y w : PureVector (KGFamilyCarrier B)),
    transitionProbability (kgRawTensor x y) (kgRawTensor z w)=transitionProbability x z*transitionProbability y w
  symmetric_comparison : Nonempty (SymmetricCategory (KGFamilyObject a))
  continuation_scalar : ∀ (q : ProperPoincareTransform) (A : KGFamilyObject a)
    (c : ℂ) (hc : c ≠ 0) (x : PureVector (KGFamilyCarrier A)),
    kgFamilyFlow q (PureVector.smul c hc x)=PureVector.smul c hc (kgFamilyFlow q x)
  continuation_weight : ∀ (q : ProperPoincareTransform) (A : KGFamilyObject a)
    (x y : PureVector (KGFamilyCarrier A)),transitionProbability (kgFamilyFlow q x) (kgFamilyFlow q y)=transitionProbability x y
  continuation_comparison : ∀ (q : ProperPoincareTransform) {A B : KGFamilyObject a}
    (f : A ⟶ B) (x : PureVector (KGFamilyCarrier A)),
    PureVector.mapUnitary f.isometry (kgFamilyFlow q x)=kgFamilyFlow q (PureVector.mapUnitary f.isometry x)
  continuation_tensor : ∀ (q : ProperPoincareTransform) (A B : KGFamilyObject a)
    (x : PureVector (KGFamilyCarrier A)) (y : PureVector (KGFamilyCarrier B)),
    kgFamilyFlow q (A := kgFamilyTensor A B) (kgRawTensor x y)=
      kgRawTensor (kgFamilyFlow q x) (kgFamilyFlow q y)
  continuation_restriction : ∀ (V : Opens CoordinatePoint) (h : Ω ≤ V)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (π : KGFamilyQuestion a Ω A),
    kgFamilyQuestionExtend h (kgFamilyFlowQuestion q π)=kgFamilyFlowQuestion q (kgFamilyQuestionExtend h π)
  complete_frame : ∀ (g : ProperPoincareTransform) (A : KGFamilyObject a)
    (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A),
    kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgFamilyFlow g x)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π))=kgFamilyOutput a s Ω A x π

theorem kg_constructed_raw_qp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGSpecificRawQP a s Ω where
  nonempty := kg_family_raw_nonempty a
  determinate A := (kgRawRegisteredOrbit a s Ω A).reference_determinate
  actual_failure := (kg_family_kernel_objecthood a s Ω).2.2.2.1
  interval _ x y := kg_raw_probability_interval x y
  registered := kg_raw_registered_probability a s Ω
  arrow_references := kg_raw_arrow_reference a s Ω
  base_references _V h := kg_raw_region_reference a s h
  scalar_one _ x := kgRawScalarAction.one_smul x
  scalar_mul _ c d x := kgRawScalarAction.mul_smul c d x
  scalar_weight _ c d x y := kg_raw_phase_probability c d x y
  scalar_record := kg_family_output_scalar a s Ω
  orbit_coequalizer _ _ f hf := kg_raw_orbit_coequalizer f hf
  open_orbit_quotient _ := kg_ray_open_quotient
  continuous_orbit_coequalizer _A _Y := by
    intro _inst f hc hf
    exact kg_raw_continuous_orbit_coequalizer f hc hf
  raw_profile_complete _ x y := kg_raw_profiles_exact_orbits x y
  independent_scalar _ _ c d hc hd x y := kg_raw_tensor_scalar_equivariance c d hc hd x y
  independent_weights _ _ x z y w := kg_raw_tensor_weights_multiply x z y w
  symmetric_comparison := ⟨inferInstance⟩
  continuation_scalar := kg_family_flow_scalar
  continuation_weight := kg_family_flow_probability
  continuation_comparison := kg_family_flow_internal_arrow
  continuation_tensor q A B x y := kg_comparison_continuation_monoidal a q A.shape B.shape x y
  continuation_restriction _ h q _ π := kg_family_flow_region_square h q π
  complete_frame g := kg_original_family_complete_frame a s g Ω

structure KGSpecificStandingSource (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) : Prop where
  raw_nonempty : ∀ A : KGFamilyObject a,Nonempty (PureVector (KGFamilyCarrier A))
  raw_weight_interval : ∀ (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)),
    0 ≤ transitionProbability x y ∧ transitionProbability x y ≤ 1
  comparison_registered : ∀ (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)),
    (kgRawRegisteredOrbit a s Ω A).kernel.standing x
      (.execution (.comparison y)) (.comparison (transitionProbability x y))
  scalar_records : ∀ (A : KGFamilyObject a) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A),
    kgFamilyOutput a s Ω A (PureVector.smul c hc x) π=kgFamilyOutput a s Ω A x π
  exact_registered_orbits : ∀ (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)),
    (kgRawRegisteredOrbit a s Ω A).SameRegisteredStanding x y ↔ rayMap _ x=rayMap _ y
  universal_standing : ∀ (A : KGFamilyObject a) (Y : Type)
    (f : PureVector (KGFamilyCarrier A) → Y),
    (∀ x y,(kgRawRegisteredOrbit a s Ω A).SameRegisteredStanding x y → f x=f y) →
      ∃! g : PhysicalRay (KGFamilyCarrier A) → Y,∀ x,g (rayMap _ x)=f x
  quotient_references : ∀ (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω A)),
    (kgRawRegisteredOrbit a s Ω A).standingReferences.referenceAt (rayMap _ x) π=
      (kgRawRegisteredOrbit a s Ω A).references.referenceAt x π
  complete_record_faithful : ∀ A : KGFamilyObject a,Function.Injective (kgW9StandingRecord a s Ω A)
  separated_probability : ∀ (A : KGFamilyObject a) (r t : PhysicalRay (KGFamilyCarrier A)),
    (∀ z,rayTransitionProbability r z=rayTransitionProbability t z) → r=t
  continuation_unique : ∀ (q : ProperPoincareTransform) (A : KGFamilyObject a),
    ∃! C : PhysicalRay (KGFamilyCarrier A) → PhysicalRay (KGFamilyCarrier A),
      ∀ x,C (rayMap _ x)=rayMap _ (kgFamilyFlow q x)
  realized_identity : ∀ (A : KGFamilyObject a) (π : KGRealizedQuestion a s Ω A),
    kgRealizedPullback a s Ω (𝟙 A) π=π
  realized_composition : ∀ {A B C : KGFamilyObject a} (f : A ⟶ B) (g : B ⟶ C)
    (π : KGRealizedQuestion a s Ω C),
    kgRealizedPullback a s Ω (f ≫ g) π=kgRealizedPullback a s Ω f (kgRealizedPullback a s Ω g π)
  complete_frame_record : ∀ (g : ProperPoincareTransform) (A : KGFamilyObject a)
    (r : PhysicalRay (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A),
    kgChartStandingRecord a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgStandingFlow g A r)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π))=kgW9StandingRecord a s Ω A r π
  frame_question_identity : ∀ (A : KGFamilyObject a) (g : ProperPoincareTransform)
    (π : KGFrameQuestion a s Ω A g),kgFrameQuestionTransport a s Ω A g g π=π
  frame_question_composition : ∀ (A : KGFamilyObject a) (g h k : ProperPoincareTransform)
    (π : KGFrameQuestion a s Ω A g),
    kgFrameQuestionTransport a s Ω A h k (kgFrameQuestionTransport a s Ω A g h π)=
      kgFrameQuestionTransport a s Ω A g k π
  arrow_references : ∀ {A B : KGStandingObject a} (f : A ⟶ B)
    (r : PhysicalRay (KGFamilyCarrier A.raw)) (π : RegisteredQuestion (KGFamilyQuestion a Ω B.raw)),
    (kgRawRegisteredOrbit a s Ω B.raw).standingReferences.referenceAt (f.stateMap r) π=
      (kgRawRegisteredOrbit a s Ω A.raw).standingReferences.referenceAt r
        (mapRegisteredQuestion (kgFamilyQuestionPullback f.rawArrow) π)
  base_references : ∀ (V : Opens CoordinatePoint) (h : Ω ≤ V) (A : KGFamilyObject a)
    (r : PhysicalRay (KGFamilyCarrier A)) (π : RegisteredQuestion (KGFamilyQuestion a Ω A)),
    (kgRawRegisteredOrbit a s V A).standingReferences.referenceAt r
      (mapRegisteredQuestion (kgFamilyQuestionExtend h) π)=
      (kgRawRegisteredOrbit a s Ω A).standingReferences.referenceAt r π
  closing_monoidal : Nonempty (kgQCloseComparison a).Monoidal
  closing_symmetric : Nonempty (kgQCloseComparison a).LaxBraided
  independent_weights : ∀ (A B : KGFamilyObject a)
    (r t : PhysicalRay (KGFamilyCarrier A)) (u v : PhysicalRay (KGFamilyCarrier B)),
    rayTransitionProbability (kgTensorRay r u) (kgTensorRay t v)=rayTransitionProbability r t*rayTransitionProbability u v
  tensor_regular : ∀ A B : KGFamilyObject a,Continuous
    (fun p : PhysicalRay (KGFamilyCarrier A) × PhysicalRay (KGFamilyCarrier B) => kgTensorRay p.1 p.2)
  original_source_square : ∀ r : PhysicalRay (fockCoreDomain a),
    kgW9OriginalResponse a s Ω r=
      (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
        (wickCommonRoleSourcePresentation a s Ω (kgOriginalQuantumToRay a r)))).val

theorem kg_constraint_first_standing_source (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGSpecificStandingSource a s Ω where
  raw_nonempty := kg_family_raw_nonempty a
  raw_weight_interval _ x y := kg_raw_probability_interval x y
  comparison_registered := kg_raw_registered_probability a s Ω
  scalar_records := kg_family_output_scalar a s Ω
  exact_registered_orbits := kg_registered_orbit_exact a s Ω
  universal_standing A _ f hf := (kgRawRegisteredOrbit a s Ω A).universal_standing_descent f hf
  quotient_references A := (kgRawRegisteredOrbit a s Ω A).standing_reference_square
  complete_record_faithful := kg_w9_standing_record_faithful a s Ω
  separated_probability _ _ _ h := ray_eq_of_transitionProfile_eq h
  continuation_unique := kg_standing_flow_unique a
  realized_identity := kg_realized_pullback_identity a s Ω
  realized_composition := kg_realized_pullback_comp a s Ω
  complete_frame_record g := kg_original_standing_complete_frame a s g Ω
  frame_question_identity := kg_frame_question_identity a s Ω
  frame_question_composition := kg_frame_question_comp a s Ω
  arrow_references := kg_standing_arrow_reference a s Ω
  base_references _V h := kg_standing_region_reference a s h
  closing_monoidal := ⟨inferInstance⟩
  closing_symmetric := ⟨inferInstance⟩
  independent_weights _ _ r t u v := kg_tensor_ray_weights r t u v
  tensor_regular _ _ := kg_tensor_ray_joint_continuous
  original_source_square := kg_w9_complete_original_source_square a s Ω

theorem kg_specific_raw_to_standing_source (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KGSpecificRawQP a s Ω ∧ KGSpecificStandingSource a s Ω :=
  ⟨kg_constructed_raw_qp a s Ω,kg_constraint_first_standing_source a s Ω⟩

end AASCKleinGordon
