import NativeCalibratedMetricFromComparisons
import KernelReference.ContextualQuotient

/-! The independent original signature here is the stated ten numerical
comparison queries, with their original real codomain. Reconstruction and
all-query recovery are proved before quotient descent. No metric or metric
factorization field is supplied in the source presentation. This is exact
for this role, not a claim that ten queries exhaust an entire physical state. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open AASC.KernelReference

variable {Source : Type*}

def nativeComparisonReceipt (observe : Source → OriginalComparisonAnswers)
    (s : Source) : ComparisonMatrix:=reconstructComparison (observe s)

theorem native_comparison_all_original_readouts_recovered
    (observe : Source → OriginalComparisonAnswers) (s : Source) :
    comparisonAnswers (nativeComparisonReceipt observe s)=observe s :=
  comparison_reconstruction_preserves_all_original_answers _

theorem native_comparison_original_protocol_graph_exact
    (observe : Source → OriginalComparisonAnswers) (s : Source) (i : Fin 10) (a : ℝ) :
    comparisonQuadratic (nativeComparisonReceipt observe s) (originalComparisonProbe i)=a ↔
      observe s i=a := by
  change comparisonAnswers (nativeComparisonReceipt observe s) i=a ↔ observe s i=a
  rw [native_comparison_all_original_readouts_recovered]

theorem native_comparison_receipt_fibres_exact
    (observe : Source → OriginalComparisonAnswers) (s t : Source) :
    nativeComparisonReceipt observe s=nativeComparisonReceipt observe t ↔
      ContextualQuotient.Equivalent observe s t := by
  constructor
  · intro same i
    have h:=congrArg comparisonAnswers same
    rw [native_comparison_all_original_readouts_recovered,
      native_comparison_all_original_readouts_recovered] at h
    exact congrFun h i
  · intro same
    exact congrArg reconstructComparison (funext same)

theorem native_comparison_unique_injective_public_kernel_descent
    (observe : Source → OriginalComparisonAnswers) :
    ∃! reduced:ContextualQuotient.CanonicalQuotient observe → ComparisonMatrix,
      (∀ s,reduced (ContextualQuotient.classify observe s)=nativeComparisonReceipt observe s) ∧
      Function.Injective reduced := by
  obtain ⟨reduced,receipt,unique⟩:=ContextualQuotient.unique_factorization observe
    (nativeComparisonReceipt observe)
    (fun s t same=>(native_comparison_receipt_fibres_exact observe s t).mpr same)
  refine ⟨reduced,⟨receipt,?_⟩,?_⟩
  · intro x y same
    obtain ⟨s,rfl⟩:=ContextualQuotient.classify_surjective observe x
    obtain ⟨t,rfl⟩:=ContextualQuotient.classify_surjective observe y
    rw [receipt,receipt] at same
    exact (ContextualQuotient.classify_eq_iff observe s t).mpr
      ((native_comparison_receipt_fibres_exact observe s t).mp same)
  · intro other ho
    exact unique other ho.1

theorem native_comparison_factors_through_every_complete_numerical_receiver
    (observe : Source → OriginalComparisonAnswers) {Receiver : Type*}
    (F : Source → Receiver) (onto : Function.Surjective F)
    (read : Receiver → OriginalComparisonAnswers) (recover : ∀ s,read (F s)=observe s) :
    ∃! reconstructed:Receiver → ComparisonMatrix,
      ∀ s,reconstructed (F s)=nativeComparisonReceipt observe s := by
  refine ⟨fun y=>reconstructComparison (read y),?_,?_⟩
  · intro s
    change reconstructComparison (read (F s))=reconstructComparison (observe s)
    rw [recover]
  · intro other ho
    funext y
    obtain ⟨s,rfl⟩:=onto y
    change other (F s)=reconstructComparison (read (F s))
    rw [ho,recover]
    rfl

theorem native_original_comparison_redescription_preserves_constructed_receipt
    (observe : Source → OriginalComparisonAnswers) (f : Source → Source)
    (lawful : ∀ s i,observe (f s) i=observe s i) (s : Source) :
    nativeComparisonReceipt observe (f s)=nativeComparisonReceipt observe s :=
  (native_comparison_receipt_fibres_exact observe (f s) s).mpr (lawful s)

theorem native_occupied_null_clock_source_constructs_nondegenerate_receipt
    (observe : Source → OriginalComparisonAnswers) (s : Source)
    (null : ∀ i:Fin 10,i≠0 → observe s i=0) (clock : 0<observe s 0) :
    (nativeComparisonReceipt observe s).transpose=nativeComparisonReceipt observe s ∧
      comparisonAnswers (nativeComparisonReceipt observe s)=observe s ∧
      (nativeComparisonReceipt observe s).det≠0 := by
  refine ⟨reconstruct_comparison_symmetric _,
    native_comparison_all_original_readouts_recovered observe s,?_⟩
  change (reconstructComparison (observe s)).det≠0
  rw [constructed_null_receipt_determinant _ null]
  exact neg_ne_zero.mpr (pow_ne_zero _ (ne_of_gt clock))

#print axioms native_comparison_all_original_readouts_recovered
#print axioms native_comparison_original_protocol_graph_exact
#print axioms native_comparison_receipt_fibres_exact
#print axioms native_comparison_unique_injective_public_kernel_descent
#print axioms native_comparison_factors_through_every_complete_numerical_receiver
#print axioms native_original_comparison_redescription_preserves_constructed_receipt
#print axioms native_occupied_null_clock_source_constructs_nondegenerate_receipt
end
end AASCMetricConstruction
