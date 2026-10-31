import KGFamilyRecordLaws

/-! On independent preparations, conditioning on the nonzero factor itself
retains every original extracted record, including its execution failure.
No factorization is asserted for arbitrary entangled preparations. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

section SameExtraction
variable {E F G Y : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem kg_conditional_same_extraction (L : E →ₗ[ℂ] G) (M : F →ₗ[ℂ] G)
    (output : PureVector G → Y) (x : PureVector E) (y : PureVector F)
    (h : L x.val=M y.val) : kgConditionalValue L output x=kgConditionalValue M output y := by
  classical
  simp only [kgConditionalValue,h]

end SameExtraction

theorem kg_product_right_original_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A B : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) (y : PureVector (KGFamilyCarrier B))
    (K : KGExtraction a A) (π : WickMetricPathRoleProtocol Ω) :
    kgFamilyOutput a s Ω (kgFamilyTensor A B) (kgRawTensor x y) (.original (.right K y.val) π)=
      kgFamilyOutput a s Ω A x (.original K π) := by
  have hc : inner ℂ y.val y.val ≠ 0 := fun hz => y.property (inner_self_eq_zero.mp hz)
  change KGFamilyReadout.extraction (kgConditionalValue _ _ _)=
    KGFamilyReadout.extraction (kgConditionalValue _ _ _)
  apply congrArg KGFamilyReadout.extraction
  refine (kg_conditional_same_extraction
    (kgExtractionMap (.right K y.val)).toLinearMap (kgExtractionMap K).toLinearMap
    (fun u => kgRawOriginalOutput a s Ω u π) (kgRawTensor x y)
    (PureVector.smul (inner ℂ y.val y.val) hc x) ?_).trans ?_
  · change kgExtractionMap K (kgRightContractionLM y.val (x.val ⊗ₜ[ℂ] y.val))=
      kgExtractionMap K ((inner ℂ y.val y.val) • x.val)
    rw [kg_right_contraction_tmul]
  · exact kg_conditional_value_scalar (kgExtractionMap K).toLinearMap
      (fun u => kgRawOriginalOutput a s Ω u π)
      (fun c hc u => kg_raw_original_output_scalar a s Ω c hc u π) _ hc x

theorem kg_product_left_original_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A B : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A)) (y : PureVector (KGFamilyCarrier B))
    (K : KGExtraction a B) (π : WickMetricPathRoleProtocol Ω) :
    kgFamilyOutput a s Ω (kgFamilyTensor A B) (kgRawTensor x y) (.original (.left x.val K) π)=
      kgFamilyOutput a s Ω B y (.original K π) := by
  have hc : inner ℂ x.val x.val ≠ 0 := fun hz => x.property (inner_self_eq_zero.mp hz)
  change KGFamilyReadout.extraction (kgConditionalValue _ _ _)=
    KGFamilyReadout.extraction (kgConditionalValue _ _ _)
  apply congrArg KGFamilyReadout.extraction
  refine (kg_conditional_same_extraction
    (kgExtractionMap (.left x.val K)).toLinearMap (kgExtractionMap K).toLinearMap
    (fun u => kgRawOriginalOutput a s Ω u π) (kgRawTensor x y)
    (PureVector.smul (inner ℂ x.val x.val) hc y) ?_).trans ?_
  · change kgExtractionMap K (kgLeftContraction x.val (x.val ⊗ₜ[ℂ] y.val))=
      kgExtractionMap K ((inner ℂ x.val x.val) • y.val)
    rw [kg_left_contraction_tmul]
  · exact kg_conditional_value_scalar (kgExtractionMap K).toLinearMap
      (fun u => kgRawOriginalOutput a s Ω u π)
      (fun c hc u => kg_raw_original_output_scalar a s Ω c hc u π) _ hc y

def kgOriginalFiniteQuestion (a : Parameters) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    KGFamilyQuestion a Ω (kgOriginalObject a) := .original .original (.original (.metric (.finite H)))

theorem kg_original_finite_rejection_output (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (outside : H ∉ wickOriginalMetricNeighborhood Ω) :
    kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u) (kgOriginalFiniteQuestion a H)=
      .extraction (some (.metric .failed)) := by
  change kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u)
    (.original .original (.original (.metric (.finite H))))=_
  rw [kg_family_original_identity,wick_metric_path_finite_failure_retained a s Ω u H outside]

theorem kg_original_finite_rejection_classified (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (outside : H ∉ wickOriginalMetricNeighborhood Ω) :
    kgExecutionFailureOf (kgFamilyOutput a s Ω (kgOriginalObject a)
      (kgRawOriginalEquiv a u) (kgOriginalFiniteQuestion a H))=some .originalMetricRejection := by
  rw [kg_original_finite_rejection_output a s Ω u H outside]
  rfl

theorem kg_original_finite_first_failure (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (u : WickNonzeroCore) (H : MetricSourceProbe Ω) (outside : H ∉ wickOriginalMetricNeighborhood Ω)
    (initial : List (KGFamilyQuestion a Ω (kgOriginalObject a)))
    (successful : ∀ π∈initial,kgExecutionFailureOf
      (kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u) π)=none) :
    kgFirstFailure (kgFamilyOutput a s Ω (kgOriginalObject a) (kgRawOriginalEquiv a u))
      (initial++[kgOriginalFiniteQuestion a H])=some (initial.length,.originalMetricRejection) := by
  rw [kg_first_failure_prefix _ initial [kgOriginalFiniteQuestion a H] successful,
    kg_first_failure_head _ (kgOriginalFiniteQuestion a H) [] .originalMetricRejection
      (kg_original_finite_rejection_classified a s Ω u H outside)]
  simp only [Option.map_some,Nat.zero_add]

end AASCKleinGordon
