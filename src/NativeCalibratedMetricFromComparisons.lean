import NativeFiniteComparisonReconstruction

/-! Construct a nondegenerate Lorentz form from actual null and clock answers.
This is the calibrated finite comparison branch of SR Lemma 12.3, not a
derivation of its comparison carrier or of quadratic physical reception. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Matrix BigOperators

def comparisonUnitLorentz : ComparisonMatrix:=Matrix.diagonal ![1,-1,-1,-1]

theorem comparison_unit_lorentz_det : comparisonUnitLorentz.det=-1 := by
  norm_num [comparisonUnitLorentz,Matrix.det_diagonal,Fin.prod_univ_succ,
    Matrix.vecCons,Fin.cases]

theorem reconstruct_null_answers (r : OriginalComparisonAnswers)
    (null : ∀ i:Fin 10,i≠0 → r i=0) :
    reconstructComparison r=(r 0) • comparisonUnitLorentz := by
  have h1:=null 1 (by decide)
  have h2:=null 2 (by decide)
  have h3:=null 3 (by decide)
  have h4:=null 4 (by decide)
  have h5:=null 5 (by decide)
  have h6:=null 6 (by decide)
  have h7:=null 7 (by decide)
  have h8:=null 8 (by decide)
  have h9:=null 9 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reconstructComparison,comparisonTimeSpace,comparisonSpatialDiagonal,
      comparisonSpatialCross,comparisonUnitLorentz,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,
      h1,h2,h3,h4,h5,h6,h7,h8,h9] <;>
    dsimp [Fin.succ,Fin.instOfNat,Fin.ofNat] at * <;> ring

theorem constructed_null_receipt_quadratic (r : OriginalComparisonAnswers)
    (null : ∀ i:Fin 10,i≠0 → r i=0) (v : ComparisonVector) :
    comparisonQuadratic (reconstructComparison r) v=
      r 0*(v 0^2-v 1^2-v 2^2-v 3^2) := by
  rw [reconstruct_null_answers r null]
  norm_num [comparisonQuadratic,comparisonUnitLorentz,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  dsimp [Fin.succ,Fin.instOfNat,Fin.ofNat] at *
  norm_num [Matrix.diagonal,Fin.ext_iff]
  ring

theorem constructed_null_receipt_determinant (r : OriginalComparisonAnswers)
    (null : ∀ i:Fin 10,i≠0 → r i=0) :
    (reconstructComparison r).det= -(r 0)^4 := by
  rw [reconstruct_null_answers r null,Matrix.det_smul,comparison_unit_lorentz_det]
  simp

theorem original_null_and_positive_clock_construct_unique_nondegenerate_receipt
    (r : OriginalComparisonAnswers) (null : ∀ i:Fin 10,i≠0 → r i=0)
    (clock : 0<r 0) :
    ∃! M:ComparisonMatrix,M.transpose=M ∧ comparisonAnswers M=r ∧
      M.det≠0 ∧ ∀ v,comparisonQuadratic M v=r 0*(v 0^2-v 1^2-v 2^2-v 3^2) := by
  refine ⟨reconstructComparison r,⟨reconstruct_comparison_symmetric r,
    comparison_reconstruction_preserves_all_original_answers r,?_,
    constructed_null_receipt_quadratic r null⟩,?_⟩
  · rw [constructed_null_receipt_determinant r null]
    exact neg_ne_zero.mpr (pow_ne_zero _ (ne_of_gt clock))
  · intro N hN
    exact (original_comparison_answers_separate_symmetric_receipts N _ hN.1
      (reconstruct_comparison_symmetric r)).mp
        (hN.2.1.trans (comparison_reconstruction_preserves_all_original_answers r).symm)

theorem every_original_comparison_query_is_necessary (k : Fin 10) :
    ∃ M N:ComparisonMatrix,M.transpose=M ∧ N.transpose=N ∧ M≠N ∧
      (∀ i,i≠k → comparisonAnswers M i=comparisonAnswers N i) := by
  let r:OriginalComparisonAnswers:=fun _=>0
  let s:OriginalComparisonAnswers:=fun i=>if i=k then 1 else 0
  refine ⟨reconstructComparison r,reconstructComparison s,
    reconstruct_comparison_symmetric r,reconstruct_comparison_symmetric s,?_,?_⟩
  · intro same
    have h:=congrFun (congrArg comparisonAnswers same) k
    rw [comparison_reconstruction_preserves_all_original_answers,
      comparison_reconstruction_preserves_all_original_answers] at h
    norm_num [r,s] at h
  · intro i hi
    rw [comparison_reconstruction_preserves_all_original_answers,
      comparison_reconstruction_preserves_all_original_answers]
    simp [r,s,hi]

#print axioms comparison_unit_lorentz_det
#print axioms reconstruct_null_answers
#print axioms constructed_null_receipt_quadratic
#print axioms constructed_null_receipt_determinant
#print axioms original_null_and_positive_clock_construct_unique_nondegenerate_receipt
#print axioms every_original_comparison_query_is_necessary
end
end AASCMetricConstruction
