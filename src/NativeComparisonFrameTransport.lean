import NativeComparisonKernelAttachment

/-! Reconstruct and transport the same finite original comparison answers
under arbitrary invertible linear coordinates. No isometry is a premise.
This is passive linear comparison transport, not general curved atlas gluing. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators

theorem comparison_quadratic_eq_dot (M : ComparisonMatrix) (v : ComparisonVector) :
    comparisonQuadratic M v=v ⬝ᵥ M *ᵥ v := by
  simp only [comparisonQuadratic,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

theorem comparison_quadratic_pullback (M B : ComparisonMatrix) (v : ComparisonVector) :
    comparisonQuadratic (B.transpose*M*B) v=comparisonQuadratic M (B *ᵥ v) := by
  calc
    _ = v ⬝ᵥ B.transpose *ᵥ (M *ᵥ (B *ᵥ v)) := by
      rw [comparison_quadratic_eq_dot]
      simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    _ = (B *ᵥ v) ⬝ᵥ M *ᵥ (B *ᵥ v) := by
      rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    _ = _ := (comparison_quadratic_eq_dot _ _).symm

def reconstructComparisonInFrame (r : OriginalComparisonAnswers)
    (inverseFrame : ComparisonMatrix) : ComparisonMatrix:=
  inverseFrame.transpose*reconstructComparison r*inverseFrame

theorem reconstructed_frame_receipt_symmetric (r : OriginalComparisonAnswers)
    (C : ComparisonMatrix) :
    (reconstructComparisonInFrame r C).transpose=reconstructComparisonInFrame r C := by
  simp only [reconstructComparisonInFrame,Matrix.transpose_mul,Matrix.transpose_transpose,
    reconstruct_comparison_symmetric,Matrix.mul_assoc]

theorem reconstructed_frame_receipt_recovers_original_queries
    (r : OriginalComparisonAnswers) (B C : ComparisonMatrix) (inverse : C*B=1) (i : Fin 10) :
    comparisonQuadratic (reconstructComparisonInFrame r C) (B *ᵥ originalComparisonProbe i)=r i := by
  rw [reconstructComparisonInFrame,comparison_quadratic_pullback,Matrix.mulVec_mulVec,
    inverse,Matrix.one_mulVec]
  exact congrFun (comparison_reconstruction_preserves_all_original_answers r) i

theorem original_transported_queries_determine_unique_symmetric_receipt
    (r : OriginalComparisonAnswers) (B C : ComparisonMatrix)
    (inverse : C*B=1) (rightInverse : B*C=1) :
    ∃! M:ComparisonMatrix,M.transpose=M ∧
      ∀ i,comparisonQuadratic M (B *ᵥ originalComparisonProbe i)=r i := by
  refine ⟨reconstructComparisonInFrame r C,
    ⟨reconstructed_frame_receipt_symmetric r C,
      reconstructed_frame_receipt_recovers_original_queries r B C inverse⟩,?_⟩
  intro N hN
  have hs:(B.transpose*N*B).transpose=B.transpose*N*B:=by
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hN.1,Matrix.mul_assoc]
  have ha:comparisonAnswers (B.transpose*N*B)=r:=by
    funext i
    exact (comparison_quadratic_pullback N B (originalComparisonProbe i)).trans (hN.2 i)
  have he:B.transpose*N*B=reconstructComparison r:=
    (original_comparison_answers_separate_symmetric_receipts _ _ hs
      (reconstruct_comparison_symmetric r)).mp
        (ha.trans (comparison_reconstruction_preserves_all_original_answers r).symm)
  have back:C.transpose*(B.transpose*N*B)*C=N:=by
    calc
      _ = (B*C).transpose*N*(B*C) := by
        simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = N := by simp [rightInverse]
  unfold reconstructComparisonInFrame
  rw [← he,back]

theorem constructed_frame_null_clock_receipt_nondegenerate
    (r : OriginalComparisonAnswers) (null : ∀ i:Fin 10,i≠0 → r i=0) (clock : 0<r 0)
    (B C : ComparisonMatrix) (rightInverse : B*C=1) :
    (reconstructComparisonInFrame r C).det≠0 := by
  have hd:B.det*C.det=1:=by
    simpa only [Matrix.det_mul,Matrix.det_one] using congrArg Matrix.det rightInverse
  have hc:C.det≠0:=by intro hz; rw [hz,mul_zero] at hd; norm_num at hd
  have hm:(reconstructComparison r).det≠0:=by
    rw [constructed_null_receipt_determinant _ null]
    exact neg_ne_zero.mpr (pow_ne_zero _ (ne_of_gt clock))
  simpa only [reconstructComparisonInFrame,Matrix.det_mul,Matrix.det_transpose] using
    mul_ne_zero (mul_ne_zero hc hm) hc

#print axioms comparison_quadratic_eq_dot
#print axioms comparison_quadratic_pullback
#print axioms reconstructed_frame_receipt_symmetric
#print axioms reconstructed_frame_receipt_recovers_original_queries
#print axioms original_transported_queries_determine_unique_symmetric_receipt
#print axioms constructed_frame_null_clock_receipt_nondegenerate
end
end AASCMetricConstruction
