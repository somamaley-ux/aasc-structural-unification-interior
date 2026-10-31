import KGExternalNaturality

/-! Change of frame for the entire conditional experiment. Both contraction
probes and the complete original protocol/admission chart are transported. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 CategoryTheory TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

section GenericFrame
variable {E F E' F' Y : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

theorem kg_right_contraction_frame (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (test : F) (z : E ⊗[ℂ] F) :
    kgRightContraction (V test) (TensorProduct.congrIsometry U V z)=U (kgRightContraction test z) := by
  have h : (kgRightContraction (V test)).toLinearMap.comp
      (TensorProduct.congrIsometry U V).toLinearMap=
      U.toLinearMap.comp (kgRightContraction test).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    change kgRightContraction (V test) ((U x) ⊗ₜ[ℂ] (V y))=
      U (kgRightContraction test (x ⊗ₜ[ℂ] y))
    rw [kg_right_contraction_apply,kg_right_contraction_tmul,
      kg_right_contraction_apply,kg_right_contraction_tmul,V.inner_map_map,U.map_smul]
  exact LinearMap.congr_fun h z

theorem kg_left_contraction_frame (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (test : E) (z : E ⊗[ℂ] F) :
    kgLeftContraction (U test) (TensorProduct.congrIsometry U V z)=V (kgLeftContraction test z) := by
  have h : (kgLeftContraction (U test)).toLinearMap.comp
      (TensorProduct.congrIsometry U V).toLinearMap=
      V.toLinearMap.comp (kgLeftContraction test).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    change kgLeftContraction (U test) ((U x) ⊗ₜ[ℂ] (V y))=
      V (kgLeftContraction test (x ⊗ₜ[ℂ] y))
    rw [kg_left_contraction_tmul,kg_left_contraction_tmul,U.inner_map_map,V.map_smul]
  exact LinearMap.congr_fun h z

theorem kg_conditional_value_frame (U : E ≃ₗᵢ[ℂ] E') (V : F ≃ₗᵢ[ℂ] F')
    (L : E →ₗ[ℂ] F) (M : E' →ₗ[ℂ] F')
    (source : PureVector F → Y) (target : PureVector F' → Y)
    (square : ∀ x,M (U x)=V (L x))
    (covariant : ∀ y,target (PureVector.mapUnitary V y)=source y) (x : PureVector E) :
    kgConditionalValue M target (PureVector.mapUnitary U x)=kgConditionalValue L source x := by
  classical
  by_cases hx : L x.val=0
  · have hm : M (U x.val)=0 := by rw [square,hx,map_zero]
    simp only [kgConditionalValue,PureVector.mapUnitary,dif_pos hx,dif_pos hm]
  · have hm : M (U x.val) ≠ 0 := by
      intro hz
      apply hx
      exact V.injective ((square x.val).symm.trans (hz.trans (map_zero V).symm))
    have pure : (⟨M (U x.val),hm⟩ : PureVector F')=PureVector.mapUnitary V ⟨L x.val,hx⟩ :=
      Subtype.ext (square x.val)
    simp only [kgConditionalValue,PureVector.mapUnitary,dif_neg hx,dif_neg hm]
    exact congrArg some ((congrArg target pure).trans (covariant ⟨L x.val,hx⟩))

end GenericFrame

def kgFrameContext {a : Parameters} (g : ProperPoincareTransform) {A : KGFamilyObject a} :
    KGExtraction a A → KGExtraction a A
  | .original => .original
  | @KGExtraction.right _ A B K test => .right (kgFrameContext g K) (kgComparisonPoincare a g B.shape test)
  | @KGExtraction.left _ A B test K => .left (kgComparisonPoincare a g A.shape test) (kgFrameContext g K)
  | .transport f K => .transport (kgFrameArrow g f) (kgFrameContext g K)
  | .flow q K => .flow (g*q*g⁻¹) (kgFrameContext g K)

attribute [local irreducible] kgCorePoincareIsometry

theorem kg_frame_context_square {a : Parameters} (g : ProperPoincareTransform)
    {A : KGFamilyObject a} (K : KGExtraction a A) (x : KGFamilyCarrier A) :
    kgExtractionMap (kgFrameContext g K) (kgComparisonPoincare a g A.shape x)=
      kgCorePoincareIsometry a g (kgExtractionMap K x) := by
  induction K with
  | original => rfl
  | @right A B K test ih =>
    change kgExtractionMap (kgFrameContext g K)
      (kgRightContraction (kgComparisonPoincare a g B.shape test)
        (TensorProduct.congrIsometry (kgComparisonPoincare a g A.shape)
          (kgComparisonPoincare a g B.shape) x))=_
    exact (congrArg (kgExtractionMap (kgFrameContext g K))
      (kg_right_contraction_frame
        (kgComparisonPoincare a g A.shape) (kgComparisonPoincare a g B.shape) test x)).trans
      (ih (kgRightContraction test x))
  | @left A B test K ih =>
    change kgExtractionMap (kgFrameContext g K)
      (kgLeftContraction (kgComparisonPoincare a g A.shape test)
        (TensorProduct.congrIsometry (kgComparisonPoincare a g A.shape)
          (kgComparisonPoincare a g B.shape) x))=_
    exact (congrArg (kgExtractionMap (kgFrameContext g K))
      (kg_left_contraction_frame
        (kgComparisonPoincare a g A.shape) (kgComparisonPoincare a g B.shape) test x)).trans
      (ih (kgLeftContraction test x))
  | @transport A B f K ih =>
    change kgExtractionMap (kgFrameContext g K)
      ((kgFrameArrow g f).isometry (kgComparisonPoincare a g _ x))=_
    have square : (kgFrameArrow g f).isometry (kgComparisonPoincare a g A.shape x)=
        kgComparisonPoincare a g B.shape (f.isometry x) := by
      rw [kg_frame_arrow_eq]
      exact f.intertwines g x
    exact (congrArg (kgExtractionMap (kgFrameContext g K)) square).trans (ih (f.isometry x))
  | @flow A q K ih =>
    change kgExtractionMap (kgFrameContext g K)
      (kgComparisonPoincare a (g*q*g⁻¹) _ (kgComparisonPoincare a g _ x))=_
    exact (congrArg (kgExtractionMap (kgFrameContext g K))
      (kg_comparison_continuation_conjugate a g q A.shape x)).trans
      (ih (kgComparisonPoincare a q A.shape x))

def kgRawChartOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : PureVector (fockCoreDomain a))
    (π : WickChartMetricPathProtocol Ω D) : WickRoleReadout :=
  wickChartMetricPathOutput a s Ω D ((kgRawOriginalEquiv a).symm x) π

attribute [local irreducible] kgRawOriginalEquiv wickChartMetricPathOutput

theorem kg_raw_chart_frame (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω))
    (x : PureVector (fockCoreDomain a)) (π : WickChartMetricPathProtocol Ω D) :
    kgRawChartOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickNativeAffineMetricTest g.left.toAdd g.right '' D)
      (PureVector.mapUnitary (kgCorePoincareIsometry a g) x)
      (wickChartMetricPathProtocolPoincare a g π)=kgRawChartOutput a s Ω D x π := by
  have same := kg_raw_original_actual_continuation a g ((kgRawOriginalEquiv a).symm x)
  rw [Equiv.apply_symm_apply] at same
  have back := congrArg (kgRawOriginalEquiv a).symm same
  rw [Equiv.symm_apply_apply] at back
  unfold kgRawChartOutput
  exact (congrArg (fun u => wickChartMetricPathOutput a s
    (wickAffineMetricRegion g.left.toAdd g.right Ω)
    (wickNativeAffineMetricTest g.left.toAdd g.right '' D) u
    (wickChartMetricPathProtocolPoincare a g π)) back).trans
      (wick_complete_metric_path_output_poincare a s g Ω D _ π)

theorem kg_raw_chart_scalar (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (fockCoreDomain a)) (π : WickChartMetricPathProtocol Ω D) :
    kgRawChartOutput a s Ω D (PureVector.smul c hc x) π=kgRawChartOutput a s Ω D x π := by
  have same : rayMap (fockCoreDomain a)
      (kgRawOriginalEquiv a ((kgRawOriginalEquiv a).symm (PureVector.smul c hc x)))=
      rayMap (fockCoreDomain a) (kgRawOriginalEquiv a ((kgRawOriginalEquiv a).symm x)) := by
    simpa only [Equiv.apply_symm_apply] using rayMap_smul (fockCoreDomain a) c hc x
  exact wick_chart_metric_path_output_same_ray a s Ω D _ _
    ((kg_raw_original_orbits a _ _).mp same) π

inductive KGChartFamilyQuestion (a : Parameters) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) where
  | comparison (probe : PureVector (KGFamilyCarrier A))
  | reverseComparison (probe : PureVector (KGFamilyCarrier A))
  | original (context : KGExtraction a A) (question : WickChartMetricPathProtocol Ω D)

def kgChartFamilyOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) :
    KGChartFamilyQuestion a Ω D A → KGFamilyReadout
  | .comparison y => .comparison (transitionProbability x y)
  | .reverseComparison y => .comparison (transitionProbability y x)
  | .original K π => .extraction (kgConditionalValue (kgExtractionMap K).toLinearMap
      (fun u => kgRawChartOutput a s Ω D u π) x)

theorem kg_chart_family_scalar (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (KGFamilyCarrier A)) (π : KGChartFamilyQuestion a Ω D A) :
    kgChartFamilyOutput a s Ω D A (PureVector.smul c hc x) π=kgChartFamilyOutput a s Ω D A x π := by
  cases π with
  | comparison y => exact congrArg KGFamilyReadout.comparison (transitionProbability_smul_left c hc x y)
  | reverseComparison y => exact congrArg KGFamilyReadout.comparison (transitionProbability_smul_right c hc y x)
  | original K π =>
    exact congrArg KGFamilyReadout.extraction (kg_conditional_value_scalar (kgExtractionMap K).toLinearMap
      (fun u => kgRawChartOutput a s Ω D u π)
      (fun c hc u => kg_raw_chart_scalar a s Ω D c hc u π) c hc x)

def kgChartRawRegisteredOrbit (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :
    RawRegisteredOrbit (PureVector (KGFamilyCarrier A)) (KGChartFamilyQuestion a Ω D A)
      KGFamilyReadout (PhysicalRay (KGFamilyCarrier A)) where
  output := kgChartFamilyOutput a s Ω D A
  succeeds := kgFamilySuccess
  weight := transitionProbability
  outgoing := KGChartFamilyQuestion.comparison
  incoming := KGChartFamilyQuestion.reverseComparison
  probabilityValue := KGFamilyReadout.comparison
  probability_injective := by intro r t h;exact KGFamilyReadout.comparison.inj h
  outgoing_output _ _ := rfl
  incoming_output _ _ := rfl
  probability_success _ := rfl
  orbit := PureVector.ScalarRel
  phase_output x y h π := by
    obtain ⟨c,hc,h⟩ := h
    have equal : PureVector.smul c hc x=y := Subtype.ext h
    rw [← equal]
    exact (kg_chart_family_scalar a s Ω D A c hc x π).symm
  raw_profiles_exact x y := (kg_raw_profiles_exact_orbits x y).trans
    (rayMap_eq_iff (KGFamilyCarrier A) x y)
  q := rayMap (KGFamilyCarrier A)
  q_surjective r := by induction r using Quotient.inductionOn with | _ x => exact ⟨x,rfl⟩
  q_fibres := rayMap_eq_iff (KGFamilyCarrier A)
  coequalizer f hf := kg_raw_orbit_coequalizer f hf

def kgChartStandingRecord (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) :=
  (kgChartRawRegisteredOrbit a s Ω D A).standingRecord

theorem kg_chart_standing_spec (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : KGChartFamilyQuestion a Ω D A) :
    kgChartStandingRecord a s Ω D A (rayMap _ x) π=kgChartFamilyOutput a s Ω D A x π :=
  (kgChartRawRegisteredOrbit a s Ω D A).standing_record_spec x π

def kgChartFamilyQuestionFrame (a : Parameters) (g : ProperPoincareTransform)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)} {A : KGFamilyObject a} :
    KGChartFamilyQuestion a Ω D A →
      KGChartFamilyQuestion a (wickAffineMetricRegion g.left.toAdd g.right Ω)
        (wickNativeAffineMetricTest g.left.toAdd g.right '' D) A
  | .comparison y => .comparison (kgFamilyFlow g y)
  | .reverseComparison y => .reverseComparison (kgFamilyFlow g y)
  | .original K π => .original (kgFrameContext g K) (wickChartMetricPathProtocolPoincare a g π)

theorem kg_chart_family_frame (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a)
    (x : PureVector (KGFamilyCarrier A)) (π : KGChartFamilyQuestion a Ω D A) :
    kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickNativeAffineMetricTest g.left.toAdd g.right '' D) A (kgFamilyFlow g x)
      (kgChartFamilyQuestionFrame a g π)=kgChartFamilyOutput a s Ω D A x π := by
  cases π with
  | comparison y => exact congrArg KGFamilyReadout.comparison (kg_family_flow_probability g A x y)
  | reverseComparison y => exact congrArg KGFamilyReadout.comparison (kg_family_flow_probability g A y x)
  | original K π =>
    exact congrArg KGFamilyReadout.extraction (kg_conditional_value_frame
      (kgComparisonPoincare a g A.shape) (kgCorePoincareIsometry a g)
      (kgExtractionMap K).toLinearMap (kgExtractionMap (kgFrameContext g K)).toLinearMap
      (fun u => kgRawChartOutput a s Ω D u π)
      (fun u => kgRawChartOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
        (wickNativeAffineMetricTest g.left.toAdd g.right '' D) u (wickChartMetricPathProtocolPoincare a g π))
      (kg_frame_context_square g K) (fun u => kg_raw_chart_frame a s g Ω D u π) x)

theorem kg_chart_standing_frame (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (A : KGFamilyObject a)
    (r : PhysicalRay (KGFamilyCarrier A)) (π : KGChartFamilyQuestion a Ω D A) :
    kgChartStandingRecord a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickNativeAffineMetricTest g.left.toAdd g.right '' D) A (kgStandingFlow g A r)
      (kgChartFamilyQuestionFrame a g π)=kgChartStandingRecord a s Ω D A r π := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgChartStandingRecord a s _ _ A (rayMap _ (kgFamilyFlow g x)) _=
      kgChartStandingRecord a s Ω D A (rayMap _ x) π
    rw [kg_chart_standing_spec,kg_chart_standing_spec]
    exact kg_chart_family_frame a s g Ω D A x π

def kgFamilyQuestionInChart {a : Parameters} {Ω : Opens CoordinatePoint} {A : KGFamilyObject a} :
    KGFamilyQuestion a Ω A → KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) A
  | .comparison y => .comparison y
  | .reverseComparison y => .reverseComparison y
  | .original K π => .original K (wickOriginalMetricPathInChart π)

theorem kg_family_original_chart_exact (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A) :
    kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω) A x (kgFamilyQuestionInChart π)=
      kgFamilyOutput a s Ω A x π := by
  cases π with
  | comparison y => rfl
  | reverseComparison y => rfl
  | original K π =>
    change KGFamilyReadout.extraction (kgConditionalValue _ _ _)=KGFamilyReadout.extraction (kgConditionalValue _ _ _)
    apply congrArg KGFamilyReadout.extraction
    have outputs : (fun u => kgRawChartOutput a s Ω (wickOriginalMetricNeighborhood Ω) u
        (wickOriginalMetricPathInChart π))=(fun u => kgRawOriginalOutput a s Ω u π) := by
      funext u
      exact wick_original_metric_path_chart_exact a s Ω _ π
    exact congrArg (fun output : PureVector (fockCoreDomain a) → WickRoleReadout =>
      kgConditionalValue (kgExtractionMap K).toLinearMap output x) outputs

theorem kg_original_family_complete_frame (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω A) :
    kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgFamilyFlow g x)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π))=kgFamilyOutput a s Ω A x π :=
  (kg_chart_family_frame a s g Ω (wickOriginalMetricNeighborhood Ω) A x (kgFamilyQuestionInChart π)).trans
    (kg_family_original_chart_exact a s Ω A x π)

theorem kg_original_family_frame_first_failure (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (word : List (KGFamilyQuestion a Ω A)) :
    kgFirstFailure (kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgFamilyFlow g x))
      (word.map (fun π => kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π)))=
      kgFirstFailure (kgFamilyOutput a s Ω A x) word :=
  kg_first_failure_map _ _ _ (kg_original_family_complete_frame a s g Ω A x) word

theorem kg_complete_frame_raw_reference (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω A)) :
    (kgChartRawRegisteredOrbit a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A).references.referenceAt (kgFamilyFlow g x)
      (mapRegisteredQuestion (fun ρ => kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart ρ)) π)=
      (kgRawRegisteredOrbit a s Ω A).references.referenceAt x π :=
  reference_from_record_square (kgRawRegisteredOrbit a s Ω A)
    (kgChartRawRegisteredOrbit a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A)
    x (kgFamilyFlow g x)
    (fun ρ => kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart ρ))
    rfl (kg_original_family_complete_frame a s g Ω A x) π

theorem kg_complete_frame_standing_reference (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A))
    (π : RegisteredQuestion (KGFamilyQuestion a Ω A)) :
    (kgChartRawRegisteredOrbit a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A).standingReferences.referenceAt
      (kgStandingFlow g A r)
      (mapRegisteredQuestion (fun ρ => kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart ρ)) π)=
      (kgRawRegisteredOrbit a s Ω A).standingReferences.referenceAt r π := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change (kgChartRawRegisteredOrbit a s _ _ A).standingReferences.referenceAt
      (rayMap _ (kgFamilyFlow g x)) _=(kgRawRegisteredOrbit a s Ω A).standingReferences.referenceAt (rayMap _ x) π
    exact ((kgChartRawRegisteredOrbit a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A).standing_reference_square
        (kgFamilyFlow g x)
        (mapRegisteredQuestion (fun ρ => kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart ρ)) π)).trans
      ((kg_complete_frame_raw_reference a s g Ω A x π).trans
        ((kgRawRegisteredOrbit a s Ω A).standing_reference_square x π).symm)

theorem kg_original_standing_complete_frame (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) (r : PhysicalRay (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω A) :
    kgChartStandingRecord a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgStandingFlow g A r)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π))=kgW9StandingRecord a s Ω A r π := by
  induction r using Quotient.inductionOn with
  | _ x =>
    change kgChartStandingRecord a s _ _ A (rayMap _ (kgFamilyFlow g x)) _=
      kgW9StandingRecord a s Ω A (rayMap _ x) π
    rw [kg_chart_standing_spec,kg_w9_standing_complete_record]
    exact kg_original_family_complete_frame a s g Ω A x π

theorem kg_complete_frame_region_naturality (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGFamilyObject a)
    (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A) :
    kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right V)
      (wickTransportedMetricDomain g.left.toAdd g.right V) A (kgFamilyFlow g x)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart (kgFamilyQuestionExtend h π)))=
    kgChartFamilyOutput a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgFamilyFlow g x)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π)) :=
  (kg_original_family_complete_frame a s g V A x (kgFamilyQuestionExtend h π)).trans
    ((kg_family_regional_output a s h A x π).trans
      (kg_original_family_complete_frame a s g Ω A x π).symm)

theorem kg_standing_frame_region_naturality (a : Parameters) (s : ℝ) (g : ProperPoincareTransform)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGFamilyObject a)
    (r : PhysicalRay (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A) :
    kgChartStandingRecord a s (wickAffineMetricRegion g.left.toAdd g.right V)
      (wickTransportedMetricDomain g.left.toAdd g.right V) A (kgStandingFlow g A r)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart (kgFamilyQuestionExtend h π)))=
    kgChartStandingRecord a s (wickAffineMetricRegion g.left.toAdd g.right Ω)
      (wickTransportedMetricDomain g.left.toAdd g.right Ω) A (kgStandingFlow g A r)
      (kgChartFamilyQuestionFrame a g (kgFamilyQuestionInChart π)) :=
  (kg_original_standing_complete_frame a s g V A r (kgFamilyQuestionExtend h π)).trans
    ((kg_standing_region_record a s h A r π).trans
      (kg_original_standing_complete_frame a s g Ω A r π).symm)

end AASCKleinGordon
