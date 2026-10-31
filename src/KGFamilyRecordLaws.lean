import KGConditionalRecordKernel

noncomputable section
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum CategoryTheory TopologicalSpace AASCSemanticExhaustion
open scoped TensorProduct
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

inductive KGExecutionFailure where
  | zeroExtraction
  | originalMetricRejection

def kgExecutionFailureOf : KGFamilyReadout → Option KGExecutionFailure
  | .comparison _ => none
  | .extraction none => some .zeroExtraction
  | .extraction (some (.metric .failed)) => some .originalMetricRejection
  | .extraction (some (.metric (.finite _))) => none
  | .extraction (some (.metric (.first _))) => none
  | .extraction (some (.probability _)) => none

def kgFamilySuccess (out : KGFamilyReadout) : Prop := kgExecutionFailureOf out=none

theorem kg_zero_extraction_is_failure :
    kgExecutionFailureOf (.extraction none)=some .zeroExtraction := rfl

theorem kg_original_rejection_is_failure :
    kgExecutionFailureOf (.extraction (some (.metric .failed)))=some .originalMetricRejection := rfl

theorem kg_zero_value_is_success : kgFamilySuccess (.comparison 0) := rfl

def kgFirstFailure {Q : Type} (output : Q → KGFamilyReadout) :
    List Q → Option (ℕ × KGExecutionFailure)
  | [] => none
  | π :: rest => match kgExecutionFailureOf (output π) with
    | some reason => some (0,reason)
    | none => (kgFirstFailure output rest).map (fun p => (p.1+1,p.2))

theorem kg_first_failure_head {Q : Type} (output : Q → KGFamilyReadout)
    (π : Q) (word : List Q) (reason : KGExecutionFailure)
    (failed : kgExecutionFailureOf (output π)=some reason) :
    kgFirstFailure output (π::word)=some (0,reason) := by
  simp only [kgFirstFailure,failed]

theorem kg_first_failure_after_success {Q : Type} (output : Q → KGFamilyReadout)
    (π : Q) (word : List Q) (successful : kgExecutionFailureOf (output π)=none) :
    kgFirstFailure output (π::word)=
      (kgFirstFailure output word).map (fun p => (p.1+1,p.2)) := by
  simp only [kgFirstFailure,successful]

theorem kg_first_failure_prefix {Q : Type} (output : Q → KGFamilyReadout)
    (initial suffix : List Q) (successful : ∀ π∈initial,kgExecutionFailureOf (output π)=none) :
    kgFirstFailure output (initial++suffix)=
      (kgFirstFailure output suffix).map (fun p => (p.1+initial.length,p.2)) := by
  induction initial with
  | nil => simp
  | cons π initial ih =>
    have head := successful π (by simp)
    have tail : ∀ ρ∈initial,kgExecutionFailureOf (output ρ)=none :=
      fun ρ hρ => successful ρ (by simp [hρ])
    simp only [List.cons_append,kgFirstFailure,head,ih tail,List.length_cons,Option.map_map]
    congr 1

theorem kg_first_failure_map {Q R : Type} (f : Q → R)
    (target : R → KGFamilyReadout) (source : Q → KGFamilyReadout)
    (square : ∀ π,target (f π)=source π) (word : List Q) :
    kgFirstFailure target (word.map f)=kgFirstFailure source word := by
  induction word with
  | nil => rfl
  | cons π rest ih => simp only [List.map_cons,kgFirstFailure,square,ih]

theorem kg_family_first_failure_scalar (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (c : ℂ) (hc : c ≠ 0) (x : PureVector (KGFamilyCarrier A))
    (word : List (KGFamilyQuestion a Ω A)) :
    kgFirstFailure (kgFamilyOutput a s Ω A (PureVector.smul c hc x)) word=
      kgFirstFailure (kgFamilyOutput a s Ω A x) word := by
  have h := kg_first_failure_map id (kgFamilyOutput a s Ω A (PureVector.smul c hc x))
    (kgFamilyOutput a s Ω A x) (kg_family_output_scalar a s Ω A c hc x) word
  simpa using h

theorem kg_family_first_failure_arrow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    {A B : KGFamilyObject a} (f : A ⟶ B) (x : PureVector (KGFamilyCarrier A))
    (word : List (KGFamilyQuestion a Ω B)) :
    kgFirstFailure (kgFamilyOutput a s Ω A x) (word.map (kgFamilyQuestionPullback f))=
      kgFirstFailure (kgFamilyOutput a s Ω B (PureVector.mapUnitary f.isometry x)) word :=
  kg_first_failure_map _ _ _ (fun π => (kg_family_arrow_output a s Ω f x π).symm) word

theorem kg_family_first_failure_regional (a : Parameters) (s : ℝ)
    {Ω V : Opens CoordinatePoint} (h : Ω ≤ V) (A : KGFamilyObject a)
    (x : PureVector (KGFamilyCarrier A)) (word : List (KGFamilyQuestion a Ω A)) :
    kgFirstFailure (kgFamilyOutput a s V A x) (word.map (kgFamilyQuestionExtend h))=
      kgFirstFailure (kgFamilyOutput a s Ω A x) word :=
  kg_first_failure_map _ _ _ (kg_family_regional_output a s h A x) word

theorem kg_extraction_transport_identity {a : Parameters} {A : KGFamilyObject a}
    (K : KGExtraction a A) : kgExtractionMap (.transport (𝟙 A) K)=kgExtractionMap K := by
  ext x;rfl

theorem kg_extraction_transport_comp {a : Parameters} {A B C : KGFamilyObject a}
    (f : A ⟶ B) (g : B ⟶ C) (K : KGExtraction a C) :
    kgExtractionMap (.transport (f ≫ g) K)=kgExtractionMap (.transport f (.transport g K)) := by
  ext x;rfl

theorem kg_family_region_arrow_square {a : Parameters} {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) {A B : KGFamilyObject a} (f : A ⟶ B) (π : KGFamilyQuestion a Ω B) :
    kgFamilyQuestionExtend h (kgFamilyQuestionPullback f π)=
      kgFamilyQuestionPullback f (kgFamilyQuestionExtend h π) := by
  cases π <;> rfl

def kgFamilyFlow {a : Parameters} (q : ProperPoincareTransform) {A : KGFamilyObject a} :
    PureVector (KGFamilyCarrier A) → PureVector (KGFamilyCarrier A) :=
  PureVector.mapUnitary (kgComparisonPoincare a q A.shape)

def kgFamilyFlowQuestion {a : Parameters} {Ω : Opens CoordinatePoint}
    (q : ProperPoincareTransform) {A : KGFamilyObject a} :
    KGFamilyQuestion a Ω A → KGFamilyQuestion a Ω A
  | .comparison y => .comparison (PureVector.mapUnitary (kgComparisonPoincare a q A.shape).symm y)
  | .reverseComparison y => .reverseComparison (PureVector.mapUnitary (kgComparisonPoincare a q A.shape).symm y)
  | .original K π => .original (.flow q K) π

theorem kg_family_flow_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (π : KGFamilyQuestion a Ω A) :
    kgFamilyOutput a s Ω A (kgFamilyFlow q x) π=
      kgFamilyOutput a s Ω A x (kgFamilyFlowQuestion q π) := by
  cases π with
  | comparison y =>
    exact congrArg KGFamilyReadout.comparison
      (kg_probability_inverse_probe (kgComparisonPoincare a q A.shape) x y)
  | reverseComparison y =>
    exact congrArg KGFamilyReadout.comparison
      (kg_probability_inverse_incoming_probe (kgComparisonPoincare a q A.shape) x y)
  | original K π => rfl

theorem kg_family_flow_scalar {a : Parameters} (q : ProperPoincareTransform)
    (A : KGFamilyObject a) (c : ℂ) (hc : c ≠ 0) (x : PureVector (KGFamilyCarrier A)) :
    kgFamilyFlow q (PureVector.smul c hc x)=PureVector.smul c hc (kgFamilyFlow q x) :=
  Subtype.ext ((kgComparisonPoincare a q A.shape).map_smul c x.val)

theorem kg_family_flow_probability {a : Parameters} (q : ProperPoincareTransform)
    (A : KGFamilyObject a) (x y : PureVector (KGFamilyCarrier A)) :
    transitionProbability (kgFamilyFlow q x) (kgFamilyFlow q y)=transitionProbability x y :=
  transitionProbability_mapUnitary (kgComparisonPoincare a q A.shape) x y

theorem kg_family_flow_internal_arrow {a : Parameters} (q : ProperPoincareTransform)
    {A B : KGFamilyObject a} (f : A ⟶ B) (x : PureVector (KGFamilyCarrier A)) :
    PureVector.mapUnitary f.isometry (kgFamilyFlow q x)=
      kgFamilyFlow q (PureVector.mapUnitary f.isometry x) := Subtype.ext (f.intertwines q x.val)

theorem kg_family_flow_region_square {a : Parameters} {Ω V : Opens CoordinatePoint}
    (h : Ω ≤ V) (q : ProperPoincareTransform) {A : KGFamilyObject a}
    (π : KGFamilyQuestion a Ω A) :
    kgFamilyQuestionExtend h (kgFamilyFlowQuestion q π)=
      kgFamilyFlowQuestion q (kgFamilyQuestionExtend h π) := by cases π <;> rfl

theorem kg_family_first_failure_flow (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (A : KGFamilyObject a) (x : PureVector (KGFamilyCarrier A))
    (word : List (KGFamilyQuestion a Ω A)) :
    kgFirstFailure (kgFamilyOutput a s Ω A x) (word.map (kgFamilyFlowQuestion q))=
      kgFirstFailure (kgFamilyOutput a s Ω A (kgFamilyFlow q x)) word :=
  kg_first_failure_map _ _ _ (fun π => (kg_family_flow_record a s Ω q A x π).symm) word

end AASCKleinGordon
