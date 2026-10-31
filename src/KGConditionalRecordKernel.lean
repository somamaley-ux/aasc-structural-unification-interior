import KGConditionalContractions
import KGComparisonGroupoid
import KGOriginalRegionalRestriction

/-! Generated conditional-readout contexts, independent of orbit standing.
The original KG protocol is evaluated only after an actual nonzero contraction.
Zero extraction and original finite rejection remain separate ledger results. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgOriginalObject (a : Parameters) : KGFamilyObject a := ⟨.kg⟩

inductive KGExtraction (a : Parameters) : KGFamilyObject a → Type where
  | original : KGExtraction a (kgOriginalObject a)
  | right {A B} (context : KGExtraction a A) (test : KGFamilyCarrier B) :
      KGExtraction a (kgFamilyTensor A B)
  | left {A B} (test : KGFamilyCarrier A) (context : KGExtraction a B) :
      KGExtraction a (kgFamilyTensor A B)
  | transport {A B} (arrow : A ⟶ B) (context : KGExtraction a B) : KGExtraction a A
  | flow {A} (q : ProperPoincareTransform) (context : KGExtraction a A) : KGExtraction a A

def kgExtractionMap {a : Parameters} {A : KGFamilyObject a} :
    KGExtraction a A → KGFamilyCarrier A →L[ℂ] fockCoreDomain a
  | .original => ContinuousLinearMap.id ℂ _
  | .right context test => (kgExtractionMap context).comp (kgRightContraction test)
  | .left test context => (kgExtractionMap context).comp (kgLeftContraction test)
  | .transport arrow context => (kgExtractionMap context).comp
      arrow.isometry.toContinuousLinearEquiv.toContinuousLinearMap
  | .flow q context => (kgExtractionMap context).comp
      (kgComparisonPoincare a q A.shape).toContinuousLinearEquiv.toContinuousLinearMap

theorem kg_extraction_original_map (a : Parameters) :
    (kgExtractionMap (KGExtraction.original (a := a))).toLinearMap=
      (LinearMap.id : fockCoreDomain a →ₗ[ℂ] fockCoreDomain a) := by
  ext x
  rfl

theorem kg_extraction_arrow_square {a : Parameters} {A B : KGFamilyObject a}
    (f : A ⟶ B) (K : KGExtraction a B) (x : KGFamilyCarrier A) :
    kgExtractionMap (.transport f K) x=kgExtractionMap K (f.isometry x) := rfl

theorem kg_extraction_flow_square {a : Parameters} {A : KGFamilyObject a}
    (q : ProperPoincareTransform) (K : KGExtraction a A) (x : KGFamilyCarrier A) :
    kgExtractionMap (.flow q K) x=kgExtractionMap K (kgComparisonPoincare a q A.shape x) := rfl

section ConditionalEvaluation
variable {E F Y : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def kgConditionalValue (L : E →ₗ[ℂ] F) (output : PureVector F → Y)
    (x : PureVector E) : Option Y := by
  classical
  exact if h : L x.val=0 then none else some (output ⟨L x.val,h⟩)

theorem kg_conditional_value_id (output : PureVector E → Y) (x : PureVector E) :
    kgConditionalValue (LinearMap.id : E →ₗ[ℂ] E) output x=some (output x) := by
  classical
  unfold kgConditionalValue
  change (if h : x.val=0 then none else some (output ⟨x.val,h⟩))=some (output x)
  rw [dif_neg x.property]

theorem kg_conditional_value_scalar (L : E →ₗ[ℂ] F) (output : PureVector F → Y)
    (phase : ∀ (c : ℂ) (hc : c ≠ 0) y,output (PureVector.smul c hc y)=output y)
    (c : ℂ) (hc : c ≠ 0) (x : PureVector E) :
    kgConditionalValue L output (PureVector.smul c hc x)=kgConditionalValue L output x := by
  classical
  by_cases hx : L x.val=0
  · simp only [kgConditionalValue,PureVector.coe_smul,map_smul,hx,smul_zero,dif_pos]
  · have hcx : c • L x.val ≠ 0 := smul_ne_zero hc hx
    simp only [kgConditionalValue,PureVector.coe_smul,map_smul,dif_neg hx,dif_neg hcx]
    exact congrArg some (phase c hc ⟨L x.val,hx⟩)

theorem kg_probability_inverse_probe (U : E ≃ₗᵢ[ℂ] F)
    (x : PureVector E) (y : PureVector F) :
    transitionProbability (PureVector.mapUnitary U x) y=
      transitionProbability x (PureVector.mapUnitary U.symm y) := by
  have cancel : PureVector.mapUnitary U (PureVector.mapUnitary U.symm y)=y :=
    Subtype.ext (U.apply_symm_apply y.val)
  simpa only [cancel] using transitionProbability_mapUnitary U x (PureVector.mapUnitary U.symm y)

theorem kg_probability_inverse_incoming_probe (U : E ≃ₗᵢ[ℂ] F)
    (x : PureVector E) (y : PureVector F) :
    transitionProbability y (PureVector.mapUnitary U x)=
      transitionProbability (PureVector.mapUnitary U.symm y) x := by
  have cancel : PureVector.mapUnitary U (PureVector.mapUnitary U.symm y)=y :=
    Subtype.ext (U.apply_symm_apply y.val)
  simpa only [cancel] using transitionProbability_mapUnitary U (PureVector.mapUnitary U.symm y) x

end ConditionalEvaluation

def kgRawOriginalOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (x : PureVector (fockCoreDomain a)) (π : WickMetricPathRoleProtocol Ω) : WickRoleReadout :=
  wickMetricPathRoleOutput a s Ω ((kgRawOriginalEquiv a).symm x) π

theorem kg_raw_original_output_scalar (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (c : ℂ) (hc : c ≠ 0) (x : PureVector (fockCoreDomain a))
    (π : WickMetricPathRoleProtocol Ω) :
    kgRawOriginalOutput a s Ω (PureVector.smul c hc x) π=kgRawOriginalOutput a s Ω x π := by
  have same := rayMap_smul (fockCoreDomain a) c hc x
  have equality : rayMap (fockCoreDomain a)
      (kgRawOriginalEquiv a ((kgRawOriginalEquiv a).symm (PureVector.smul c hc x))) =
      rayMap (fockCoreDomain a) (kgRawOriginalEquiv a ((kgRawOriginalEquiv a).symm x)) := by
    simpa only [Equiv.apply_symm_apply] using same
  exact (kg_raw_same_original_equivalence a s Ω _ _).mp equality π

inductive KGFamilyQuestion (a : Parameters) (Ω : Opens CoordinatePoint) (A : KGFamilyObject a) where
  | comparison (probe : PureVector (KGFamilyCarrier A))
  | reverseComparison (probe : PureVector (KGFamilyCarrier A))
  | original (context : KGExtraction a A) (question : WickMetricPathRoleProtocol Ω)

inductive KGFamilyReadout where
  | comparison (value : ℝ)
  | extraction (value : Option WickRoleReadout)

def kgFamilyOutput (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) :
    KGFamilyQuestion a Ω A → KGFamilyReadout
  | .comparison y => .comparison (transitionProbability x y)
  | .reverseComparison y => .comparison (transitionProbability y x)
  | .original K π => .extraction (kgConditionalValue (kgExtractionMap K).toLinearMap
      (fun u => kgRawOriginalOutput a s Ω u π) x)

theorem kg_family_output_scalar (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (c : ℂ) (hc : c ≠ 0)
    (x : PureVector (KGFamilyCarrier A)) (π : KGFamilyQuestion a Ω A) :
    kgFamilyOutput a s Ω A (PureVector.smul c hc x) π=kgFamilyOutput a s Ω A x π := by
  cases π with
  | comparison y => exact congrArg KGFamilyReadout.comparison (transitionProbability_smul_left c hc x y)
  | reverseComparison y => exact congrArg KGFamilyReadout.comparison (transitionProbability_smul_right c hc y x)
  | original K π =>
    exact congrArg KGFamilyReadout.extraction
      (kg_conditional_value_scalar (kgExtractionMap K).toLinearMap (fun u => kgRawOriginalOutput a s Ω u π)
        (fun d hd u => kg_raw_original_output_scalar a s Ω d hd u π) c hc x)

attribute [local irreducible] kgRawOriginalEquiv

theorem kg_family_original_identity (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) (π : WickMetricPathRoleProtocol Ω) :
    kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u) (.original .original π)=
      .extraction (some (wickMetricPathRoleOutput a s Ω u π)) := by
  change KGFamilyReadout.extraction
    (kgConditionalValue (kgExtractionMap (KGExtraction.original (a := a))).toLinearMap
      (fun x => kgRawOriginalOutput a s Ω x π) (kgRawOriginalEquiv a u))=_
  rw [kg_extraction_original_map,kg_conditional_value_id]
  unfold kgRawOriginalOutput
  rw [Equiv.symm_apply_apply]

def kgFamilyQuestionPullback {a : Parameters} {Ω : Opens CoordinatePoint}
    {A B : KGFamilyObject a} (f : A ⟶ B) : KGFamilyQuestion a Ω B → KGFamilyQuestion a Ω A
  | .comparison y => .comparison (PureVector.mapUnitary f.isometry.symm y)
  | .reverseComparison y => .reverseComparison (PureVector.mapUnitary f.isometry.symm y)
  | .original K π => .original (.transport f K) π

theorem kg_family_arrow_output (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGFamilyObject a} (f : A ⟶ B) (x : PureVector (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω B) :
    kgFamilyOutput a s Ω B (PureVector.mapUnitary f.isometry x) π=
      kgFamilyOutput a s Ω A x (kgFamilyQuestionPullback f π) := by
  cases π with
  | comparison y => exact congrArg KGFamilyReadout.comparison (kg_probability_inverse_probe f.isometry x y)
  | reverseComparison y => exact congrArg KGFamilyReadout.comparison (kg_probability_inverse_incoming_probe f.isometry x y)
  | original K π => rfl

def kgFamilyQuestionExtend {a : Parameters} {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) {A : KGFamilyObject a} : KGFamilyQuestion a Ω A → KGFamilyQuestion a V A
  | .comparison y => .comparison y
  | .reverseComparison y => .reverseComparison y
  | .original K π => .original K (kgExtendOriginalProtocol h π)

theorem kg_family_regional_output (a : Parameters) (s : ℝ) {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω A) :
    kgFamilyOutput a s V A x (kgFamilyQuestionExtend h π)=kgFamilyOutput a s Ω A x π := by
  cases π with
  | comparison y => rfl
  | reverseComparison y => rfl
  | original K π =>
    change KGFamilyReadout.extraction (kgConditionalValue (kgExtractionMap K).toLinearMap
      (fun u => kgRawOriginalOutput a s V u (kgExtendOriginalProtocol h π)) x)=
      KGFamilyReadout.extraction (kgConditionalValue (kgExtractionMap K).toLinearMap
        (fun u => kgRawOriginalOutput a s Ω u π) x)
    unfold kgConditionalValue
    split
    · rfl
    · exact congrArg (fun z => KGFamilyReadout.extraction (some z))
        (kg_complete_original_regional_output a s h _ π)

end AASCKleinGordon
