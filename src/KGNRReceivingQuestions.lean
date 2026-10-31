import KGNRConservativeRecords

/-! The declared NR-compatible comparison class and evaluated receiving questions.
The comparison hypotheses are operator squares; record laws are derived. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KGNRObject (a : Parameters) where
  shape : KGComparisonObject

def KGNRObject.raw {a : Parameters} (A : KGNRObject a) : KGFamilyObject a := ⟨A.shape⟩
abbrev KGNRCarrier {a : Parameters} (A : KGNRObject a) := KGSpatialFamilyCarrier a A.shape

structure KGNRArrow {a : Parameters} (A B : KGNRObject a) where
  lift : KGSpatialComparisonLift a A.shape B.shape
  compatible : KGNRLiftCompatible lift

def KGNRArrow.rawArrow {a : Parameters} {A B : KGNRObject a} (f : KGNRArrow A B) :
    A.raw ⟶ B.raw := f.lift.original

@[ext] theorem kg_nr_arrow_ext {a : Parameters} {A B : KGNRObject a}
    {f g : KGNRArrow A B} (h : f.rawArrow = g.rawArrow) : f = g := by
  have hs := kg_spatial_lift_faithful a A.shape B.shape f.lift g.lift h
  cases f with | mk fl hf =>
    cases g with | mk gl hg =>
      cases fl; cases gl; cases h; cases hs; rfl

def kgNRIdentity {a : Parameters} (A : KGNRObject a) : KGNRArrow A A :=
  ⟨kgSpatialIdentityLift a A.shape,kg_nr_identity_lift_compatible a A.shape⟩

def kgNRCompose {a : Parameters} {A B C : KGNRObject a}
    (f : KGNRArrow A B) (g : KGNRArrow B C) : KGNRArrow A C :=
  ⟨kgSpatialComposeLift f.lift g.lift,
    kg_nr_compose_lift_compatible f.lift g.lift f.compatible g.compatible⟩

def kgNRInverse {a : Parameters} {A B : KGNRObject a} (f : KGNRArrow A B) : KGNRArrow B A :=
  ⟨kgSpatialInverseLift f.lift,kg_nr_inverse_lift_compatible f.lift f.compatible⟩

instance kgNRGroupoid (a : Parameters) : Groupoid (KGNRObject a) where
  Hom := KGNRArrow
  id := kgNRIdentity
  comp := kgNRCompose
  id_comp f := by apply kg_nr_arrow_ext; exact Category.id_comp f.rawArrow
  comp_id f := by apply kg_nr_arrow_ext; exact Category.comp_id f.rawArrow
  assoc f g h := by apply kg_nr_arrow_ext; exact Category.assoc f.rawArrow g.rawArrow h.rawArrow
  inv := kgNRInverse
  inv_comp f := by apply kg_nr_arrow_ext; exact Groupoid.inv_comp f.rawArrow
  comp_inv f := by apply kg_nr_arrow_ext; exact Groupoid.comp_inv f.rawArrow

def kgNRIso {a : Parameters} {A B : KGNRObject a} (f : A ⟶ B) : A ≅ B :=
  ⟨f,Groupoid.inv f,Groupoid.comp_inv f,Groupoid.inv_comp f⟩

def kgNRTensor {a : Parameters} (A B : KGNRObject a) : KGNRObject a := ⟨.tensor A.shape B.shape⟩
def kgNRTensorArrow {a : Parameters} {A B C D : KGNRObject a}
    (f : A ⟶ B) (g : C ⟶ D) : kgNRTensor A C ⟶ kgNRTensor B D :=
  ⟨kgSpatialTensorLift f.lift g.lift,
    kg_nr_tensor_lift_compatible f.lift g.lift f.compatible g.compatible⟩

instance kgNRMonoidalStruct (a : Parameters) : MonoidalCategoryStruct (KGNRObject a) where
  tensorObj := kgNRTensor
  tensorHom := kgNRTensorArrow
  whiskerLeft A {_B _C} f := kgNRTensorArrow (𝟙 A) f
  whiskerRight {_A _B} f C := kgNRTensorArrow f (𝟙 C)
  tensorUnit := ⟨.unit⟩
  associator A B C := kgNRIso ⟨kgSpatialAssociatorLift a A.shape B.shape C.shape,
    kg_nr_associator_lift_compatible a A.shape B.shape C.shape⟩
  leftUnitor A := kgNRIso ⟨kgSpatialLeftUnitorLift a A.shape,
    kg_nr_left_unitor_lift_compatible a A.shape⟩
  rightUnitor A := kgNRIso ⟨kgSpatialRightUnitorLift a A.shape,
    kg_nr_right_unitor_lift_compatible a A.shape⟩

instance kgNRMonoidal (a : Parameters) : MonoidalCategory (KGNRObject a) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun A B => by
      apply kg_nr_arrow_ext; exact kg_internal_tensor_identity A.raw B.raw)
    (id_tensorHom := fun _ {_B _C} _ => rfl)
    (tensorHom_id := fun {_A _B} _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f g h k => by
      apply kg_nr_arrow_ext; exact (kg_internal_tensor_comp f.rawArrow h.rawArrow g.rawArrow k.rawArrow).symm)
    (associator_naturality := fun f g h => by
      apply kg_nr_arrow_ext; exact kg_family_associator_naturality f.rawArrow g.rawArrow h.rawArrow)
    (leftUnitor_naturality := fun f => by
      apply kg_nr_arrow_ext; exact kg_family_left_unitor_naturality f.rawArrow)
    (rightUnitor_naturality := fun f => by
      apply kg_nr_arrow_ext; exact kg_family_right_unitor_naturality f.rawArrow)
    (pentagon := fun A B C D => by
      apply kg_nr_arrow_ext; exact (kg_family_pentagon A.raw B.raw C.raw D.raw).symm)
    (triangle := fun A B => by
      apply kg_nr_arrow_ext; exact kg_family_triangle A.raw B.raw)

instance kgNRSymmetric (a : Parameters) : SymmetricCategory (KGNRObject a) where
  braiding A B := kgNRIso ⟨kgSpatialSymmetryLift a A.shape B.shape,
    kg_nr_symmetry_lift_compatible a A.shape B.shape⟩
  braiding_naturality_right A {_B _C} f := by
    apply kg_nr_arrow_ext; exact kg_family_symmetry_naturality (𝟙 A.raw) f.rawArrow
  braiding_naturality_left {_A _B} f B := by
    apply kg_nr_arrow_ext; exact kg_family_symmetry_naturality f.rawArrow (𝟙 B.raw)
  hexagon_forward A B C := by
    apply kg_nr_arrow_ext; exact kg_family_hexagon A.raw B.raw C.raw
  hexagon_reverse A B C := by
    apply kg_nr_arrow_ext; exact kg_family_reverse_hexagon A.raw B.raw C.raw
  symmetry A B := by
    apply kg_nr_arrow_ext; exact kg_family_symmetry_involutive A.raw B.raw

def KGNRRealizedQuestion (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGNRObject a) :=
  {f : PureVector (KGNRCarrier A) → KGFamilyReadout //
    ∃ q : KGNRReceivingQuestion a Ω A.shape, f = fun x => kgNRReceivingOutput a s Ω A.shape x q}

def kgNRRealizedPullback (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGNRObject a} (f : A ⟶ B) (q : KGNRRealizedQuestion a s Ω B) :
    KGNRRealizedQuestion a s Ω A := by
  refine ⟨fun x => q.val (PureVector.mapUnitary f.lift.spatial x),?_⟩
  obtain ⟨r,hr⟩ := q.prop
  refine ⟨kgNRQuestionPullback f.lift r,?_⟩
  funext x
  rw [hr]
  exact kg_nr_receiving_comparison_record a s Ω A.shape B.shape f.lift f.compatible x r

theorem kg_nr_realized_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    kgNRRealizedPullback a s Ω (𝟙 A) q = q := by apply Subtype.ext; funext x; rfl

theorem kg_nr_realized_composition (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B C : KGNRObject a} (f : A ⟶ B) (g : B ⟶ C) (q : KGNRRealizedQuestion a s Ω C) :
    kgNRRealizedPullback a s Ω (f ≫ g) q =
      kgNRRealizedPullback a s Ω f (kgNRRealizedPullback a s Ω g q) := by
  apply Subtype.ext; funext x; rfl

def kgNRRealizedFlow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (t : ℝ) (A : KGNRObject a) (q : KGNRRealizedQuestion a s Ω A) :
    KGNRRealizedQuestion a s Ω A := by
  refine ⟨fun x => q.val (PureVector.mapUnitary (kgNRSpatialFamilyFlow a t A.shape) x),?_⟩
  obtain ⟨r,hr⟩ := q.prop
  refine ⟨kgNRQuestionAdvance t r,?_⟩
  funext x
  rw [hr]
  exact kg_nr_receiving_continuation_record a s t Ω A.shape x r

theorem kg_nr_realized_flow_arrow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (t : ℝ) {A B : KGNRObject a} (f : A ⟶ B) (q : KGNRRealizedQuestion a s Ω B) :
    kgNRRealizedPullback a s Ω f (kgNRRealizedFlow a s Ω t B q) =
      kgNRRealizedFlow a s Ω t A (kgNRRealizedPullback a s Ω f q) := by
  apply Subtype.ext
  funext x
  exact congrArg q.val (Subtype.ext (f.compatible t x.val)).symm

theorem kg_nr_receiving_ray_regular (a : Parameters) (A : KGNRObject a) (t : ℝ) :
    Continuous (unitaryRayMap (kgNRSpatialFamilyFlow a t A.shape)) :=
  kg_ray_unitary_continuous _

theorem kg_nr_receiving_orbit_open (a : Parameters) (A : KGNRObject a) :
    IsOpenQuotientMap (rayMap (KGNRCarrier A)) := kg_ray_open_quotient

theorem kg_nr_receiving_tensor_regular (a : Parameters) (A B : KGNRObject a) :
    Continuous (fun p : PhysicalRay (KGNRCarrier A) × PhysicalRay (KGNRCarrier B) =>
      kgTensorRay p.1 p.2) := kg_tensor_ray_joint_continuous

end AASCKleinGordon
