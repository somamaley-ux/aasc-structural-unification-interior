import KGFrameConditionalRecords

/-! External frame coherence on realized questions. A frame label g denotes
exactly the original physical neighborhood transported by g. The semantic
functions below are proved to be those actual chart readouts, including failure. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgFrameCarrierArrow (a : Parameters) (A : KGFamilyObject a)
    (g h : ProperPoincareTransform) : KGFamilyCarrier A ≃ₗᵢ[ℂ] KGFamilyCarrier A :=
  (kgComparisonPoincare a g A.shape).symm.trans (kgComparisonPoincare a h A.shape)

theorem kg_frame_carrier_is_poincare (a : Parameters) (A : KGFamilyObject a)
    (g h : ProperPoincareTransform) :
    kgFrameCarrierArrow a A g h=kgComparisonPoincare a (h*g⁻¹) A.shape := by
  ext x
  have leftInverse := kg_comparison_continuation_mul a g g⁻¹ A.shape x
  rw [mul_inv_cancel,kg_comparison_continuation_one] at leftInverse
  have inverse : (kgComparisonPoincare a g A.shape).symm x=kgComparisonPoincare a g⁻¹ A.shape x := by
    apply (kgComparisonPoincare a g A.shape).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact leftInverse
  exact (congrArg (kgComparisonPoincare a h A.shape) inverse).trans
    (kg_comparison_continuation_mul a h g⁻¹ A.shape x).symm

theorem kg_frame_carrier_identity (a : Parameters) (A : KGFamilyObject a) (g : ProperPoincareTransform) :
    kgFrameCarrierArrow a A g g=LinearIsometryEquiv.refl ℂ _ := by
  ext x
  exact (kgComparisonPoincare a g A.shape).apply_symm_apply x

theorem kg_frame_carrier_comp (a : Parameters) (A : KGFamilyObject a)
    (g h k : ProperPoincareTransform) :
    (kgFrameCarrierArrow a A g h).trans (kgFrameCarrierArrow a A h k)=kgFrameCarrierArrow a A g k := by
  ext x
  change kgComparisonPoincare a k A.shape
    ((kgComparisonPoincare a h A.shape).symm
      (kgComparisonPoincare a h A.shape ((kgComparisonPoincare a g A.shape).symm x)))=_
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

def KGFrameQuestion (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) :=
  {f : PureVector (KGFamilyCarrier A) → KGFamilyReadout //
    ∃ π : KGFamilyQuestion a Ω A,f=fun x => kgFamilyOutput a s Ω A
      (PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm x) π}

def kgFrameQuestionOf (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFamilyQuestion a Ω A) :
    KGFrameQuestion a s Ω A g := ⟨_,π,rfl⟩

theorem kg_frame_question_actual_chart (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFamilyQuestion a Ω A)
    (x : PureVector (KGFamilyCarrier A)) :
    (kgFrameQuestionOf a s Ω A g π).val x=
      kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
        (wickTransportedMetricDomain g.left.toAdd g.right Ω) A x
        (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π)) := by
  have cancel : kgFamilyFlow g
      (PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm x)=x :=
    Subtype.ext ((kgComparisonPoincare a g A.shape).apply_symm_apply x.val)
  have square := kg_original_family_complete_frame a s g Ω A
    (PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm x) π
  rw [cancel] at square
  exact square.symm

def kgFrameQuestionTransport (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g h : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    KGFrameQuestion a s Ω A h := by
  refine ⟨fun x => π.val (PureVector.mapUnitary (kgFrameCarrierArrow a A h g) x),?_⟩
  obtain ⟨ρ,hρ⟩ := π.property
  refine ⟨ρ,?_⟩
  funext x
  rw [hρ]
  have cancel : PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm
      (PureVector.mapUnitary (kgFrameCarrierArrow a A h g) x)=
      PureVector.mapUnitary (kgComparisonPoincare a h A.shape).symm x :=
    Subtype.ext ((kgComparisonPoincare a g A.shape).symm_apply_apply
      ((kgComparisonPoincare a h A.shape).symm x.val))
  exact congrArg (fun y => kgFamilyOutput a s Ω A y ρ) cancel

theorem kg_frame_question_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    kgFrameQuestionTransport a s Ω A g g π=π := by
  apply Subtype.ext
  funext x
  exact congrArg π.val (Subtype.ext ((kgComparisonPoincare a g A.shape).apply_symm_apply x.val))

theorem kg_frame_question_comp (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g h k : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    kgFrameQuestionTransport a s Ω A h k (kgFrameQuestionTransport a s Ω A g h π)=
      kgFrameQuestionTransport a s Ω A g k π := by
  apply Subtype.ext
  funext x
  apply congrArg π.val
  apply Subtype.ext
  change kgComparisonPoincare a g A.shape
    ((kgComparisonPoincare a h A.shape).symm
      (kgComparisonPoincare a h A.shape ((kgComparisonPoincare a k A.shape).symm x.val)))=_
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem kg_frame_question_inverse (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g h : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    kgFrameQuestionTransport a s Ω A h g (kgFrameQuestionTransport a s Ω A g h π)=π :=
  (kg_frame_question_comp a s Ω A g h g π).trans (kg_frame_question_identity a s Ω A g π)

structure KGFrameLabel where
  frame : ProperPoincareTransform

instance kgFrameLabelGroupoid : Groupoid KGFrameLabel where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  inv _ := PUnit.unit

def kgFrameQuestionFunctor (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) : KGFrameLabel ⥤ Type where
  obj g := KGFrameQuestion a s Ω A g.frame
  map {_g _h} _ := kgFrameQuestionTransport a s Ω A _g.frame _h.frame
  map_id g := funext (kg_frame_question_identity a s Ω A g.frame)
  map_comp {_g _h _k} _ _ :=
    (funext (kg_frame_question_comp a s Ω A _g.frame _h.frame _k.frame)).symm

theorem kg_frame_question_record_square (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g h : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g)
    (x : PureVector (KGFamilyCarrier A)) :
    (kgFrameQuestionTransport a s Ω A g h π).val
      (PureVector.mapUnitary (kgFrameCarrierArrow a A g h) x)=π.val x := by
  apply congrArg π.val
  apply Subtype.ext
  change kgComparisonPoincare a g A.shape
    ((kgComparisonPoincare a h A.shape).symm
      (kgComparisonPoincare a h A.shape ((kgComparisonPoincare a g A.shape).symm x.val)))=x.val
  rw [LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.apply_symm_apply]

theorem kg_frame_question_scalar (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g)
    (c : ℂ) (hc : c ≠ 0) (x : PureVector (KGFamilyCarrier A)) :
    π.val (PureVector.smul c hc x)=π.val x := by
  obtain ⟨ρ,hρ⟩ := π.property
  rw [hρ]
  change kgFamilyOutput a s Ω A
    (PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm (PureVector.smul c hc x)) ρ=
    kgFamilyOutput a s Ω A (PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm x) ρ
  have equivariant : PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm
      (PureVector.smul c hc x)=PureVector.smul c hc
        (PureVector.mapUnitary (kgComparisonPoincare a g A.shape).symm x) :=
    Subtype.ext ((kgComparisonPoincare a g A.shape).symm.map_smul c x.val)
  rw [equivariant]
  exact kg_family_output_scalar a s Ω A c hc _ ρ

def kgFrameStandingReadout (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    PhysicalRay (KGFamilyCarrier A) → KGFamilyReadout :=
  (kgRawRegisteredOrbit a s Ω A).descend π.val (by
    intro x y h
    obtain ⟨c,hc,h⟩ := h
    have eq : PureVector.smul c hc x=y := Subtype.ext h
    rw [← eq]
    exact (kg_frame_question_scalar a s Ω A g π c hc x).symm)

theorem kg_frame_standing_readout_spec (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g)
    (x : PureVector (KGFamilyCarrier A)) :
    kgFrameStandingReadout a s Ω A g π (rayMap _ x)=π.val x :=
  (kgRawRegisteredOrbit a s Ω A).descend_spec _ _ x

theorem kg_frame_standing_record_square (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g h : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g)
    (r : PhysicalRay (KGFamilyCarrier A)) :
    kgFrameStandingReadout a s Ω A h (kgFrameQuestionTransport a s Ω A g h π)
      (unitaryRayMap (kgFrameCarrierArrow a A g h) r)=kgFrameStandingReadout a s Ω A g π r := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgFrameStandingReadout a s Ω A h _
      (rayMap _ (PureVector.mapUnitary (kgFrameCarrierArrow a A g h) x))=
      kgFrameStandingReadout a s Ω A g π (rayMap _ x)
    rw [kg_frame_standing_readout_spec,kg_frame_standing_readout_spec]
    exact kg_frame_question_record_square a s Ω A g h π x

theorem kg_frame_standing_readout_actual_chart (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFamilyQuestion a Ω A)
    (r : PhysicalRay (KGFamilyCarrier A)) :
    kgFrameStandingReadout a s Ω A g (kgFrameQuestionOf a s Ω A g π) r=
      kgChartStandingRecord a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
        (wickTransportedMetricDomain g.left.toAdd g.right Ω) A r
        (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π)) := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgFrameStandingReadout a s Ω A g _ (rayMap _ x)=kgChartStandingRecord a s _ _ A (rayMap _ x) _
    rw [kg_frame_standing_readout_spec,kg_chart_standing_spec]
    exact kg_frame_question_actual_chart a s Ω A g π x

def kgFrameQuestionRegion (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    KGFrameQuestion a s V A g := by
  refine ⟨π.val,?_⟩
  obtain ⟨ρ,hρ⟩ := π.property
  refine ⟨kgFamilyQuestionExtend h ρ,?_⟩
  funext x
  rw [hρ]
  exact (kg_family_regional_output a s h A _ ρ).symm

theorem kg_frame_question_region_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (g : ProperPoincareTransform) (π : KGFrameQuestion a s Ω A g) :
    kgFrameQuestionRegion a s (le_refl Ω) A g π=π := by apply Subtype.ext;rfl

theorem kg_frame_question_region_comp (a : Parameters) (s : ℝ) {Ω V W : Opens CoordinatePoint}
    (h : Ω ≤ V) (k : V ≤ W) (A : KGFamilyObject a) (g : ProperPoincareTransform)
    (π : KGFrameQuestion a s Ω A g) :
    kgFrameQuestionRegion a s (le_trans h k) A g π=
      kgFrameQuestionRegion a s k A g (kgFrameQuestionRegion a s h A g π) := by apply Subtype.ext;rfl

theorem kg_frame_question_region_naturality (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (inclusion : Ω ≤ V) (A : KGFamilyObject a) (g h : ProperPoincareTransform)
    (π : KGFrameQuestion a s Ω A g) :
    kgFrameQuestionRegion a s inclusion A h (kgFrameQuestionTransport a s Ω A g h π)=
      kgFrameQuestionTransport a s V A g h (kgFrameQuestionRegion a s inclusion A g π) := by
  apply Subtype.ext;rfl

end AASCKleinGordon
