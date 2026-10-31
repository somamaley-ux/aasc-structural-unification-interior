import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! SR Lemma 12.3, PDF 57--58: construct a symmetric quadratic receipt
from ten fixed numerical comparison answers, before assuming any metric.
The diagonal null probes are positively rescaled by sqrt(2).
These finite answers separate the quadratic receiving class only. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Matrix BigOperators

abbrev ComparisonVector := Fin 4 → ℝ
abbrev ComparisonMatrix := Matrix (Fin 4) (Fin 4) ℝ
abbrev OriginalComparisonAnswers := Fin 10 → ℝ

def originalComparisonProbe (i : Fin 10) : ComparisonVector :=
  match i.val with
  | 0 => ![1,0,0,0]
  | 1 => ![1,1,0,0]
  | 2 => ![1,-1,0,0]
  | 3 => ![1,0,1,0]
  | 4 => ![1,0,-1,0]
  | 5 => ![1,0,0,1]
  | 6 => ![1,0,0,-1]
  | 7 => ![Real.sqrt 2,1,1,0]
  | 8 => ![Real.sqrt 2,1,0,1]
  | _ => ![Real.sqrt 2,0,1,1]

def comparisonQuadratic (M : ComparisonMatrix) (v : ComparisonVector) : ℝ :=
  ∑ a,∑ b,v a*M a b*v b

def comparisonAnswers (M : ComparisonMatrix) : OriginalComparisonAnswers :=
  fun i=>comparisonQuadratic M (originalComparisonProbe i)

def comparisonTimeSpace (r : OriginalComparisonAnswers) (i : Fin 3) : ℝ :=
  match i.val with
  | 0 => (r 1-r 2)/4
  | 1 => (r 3-r 4)/4
  | _ => (r 5-r 6)/4

def comparisonSpatialDiagonal (r : OriginalComparisonAnswers) (i : Fin 3) : ℝ :=
  match i.val with
  | 0 => (r 1+r 2)/2-r 0
  | 1 => (r 3+r 4)/2-r 0
  | _ => (r 5+r 6)/2-r 0

def comparisonSpatialCross (r : OriginalComparisonAnswers) (k : Fin 10)
    (i j : Fin 3) : ℝ :=
  (r k-2*r 0-2*Real.sqrt 2*(comparisonTimeSpace r i+comparisonTimeSpace r j)
    -comparisonSpatialDiagonal r i-comparisonSpatialDiagonal r j)/2

def reconstructComparison (r : OriginalComparisonAnswers) : ComparisonMatrix :=
  let b:=comparisonTimeSpace r
  let d:=comparisonSpatialDiagonal r
  let c12:=comparisonSpatialCross r 7 0 1
  let c13:=comparisonSpatialCross r 8 0 2
  let c23:=comparisonSpatialCross r 9 1 2
  !![r 0,b 0,b 1,b 2;
     b 0,d 0,c12,c13;
     b 1,c12,d 1,c23;
     b 2,c13,c23,d 2]

theorem reconstruct_comparison_symmetric (r : OriginalComparisonAnswers) :
    (reconstructComparison r).transpose=reconstructComparison r := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem comparison_reconstruction_preserves_all_original_answers
    (r : OriginalComparisonAnswers) : comparisonAnswers (reconstructComparison r)=r := by
  funext i
  fin_cases i <;>
    norm_num [comparisonAnswers,comparisonQuadratic,originalComparisonProbe,
      reconstructComparison,comparisonTimeSpace,comparisonSpatialDiagonal,
      comparisonSpatialCross,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] <;>
    try ring_nf
  all_goals dsimp [Fin.succ,Fin.instOfNat,Fin.ofNat] at *
  all_goals try simp only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  all_goals first | rfl | ring

theorem comparison_reconstruction_recovers_every_symmetric_receipt
    (M : ComparisonMatrix) (symmetric : M.transpose=M) :
    reconstructComparison (comparisonAnswers M)=M := by
  have hm (i j:Fin 4):M j i=M i j:=congrArg (fun A:ComparisonMatrix=>A i j) symmetric
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [comparisonAnswers,comparisonQuadratic,originalComparisonProbe,
      reconstructComparison,comparisonTimeSpace,comparisonSpatialDiagonal,
      comparisonSpatialCross,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] <;>
    simp only [hm 0 1,hm 0 2,hm 0 3,hm 1 2,hm 1 3,hm 2 3] <;>
    try ring_nf
  all_goals dsimp [Fin.succ,Fin.instOfNat,Fin.ofNat] at *
  all_goals try simp only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  all_goals nlinarith only [hm 0 1,hm 0 2,hm 0 3,hm 1 2,hm 1 3,hm 2 3]

theorem original_comparison_answers_separate_symmetric_receipts
    (M N : ComparisonMatrix) (hm : M.transpose=M) (hn : N.transpose=N) :
    comparisonAnswers M=comparisonAnswers N ↔ M=N := by
  constructor
  · intro same
    rw [← comparison_reconstruction_recovers_every_symmetric_receipt M hm,
      ← comparison_reconstruction_recovers_every_symmetric_receipt N hn,same]
  · exact congrArg comparisonAnswers

theorem original_comparison_answers_have_unique_symmetric_receipt
    (r : OriginalComparisonAnswers) :
    ∃! M:ComparisonMatrix,M.transpose=M ∧ comparisonAnswers M=r := by
  refine ⟨reconstructComparison r,⟨reconstruct_comparison_symmetric r,
    comparison_reconstruction_preserves_all_original_answers r⟩,?_⟩
  intro N hn
  exact (original_comparison_answers_separate_symmetric_receipts N _ hn.1
    (reconstruct_comparison_symmetric r)).mp
      (hn.2.trans (comparison_reconstruction_preserves_all_original_answers r).symm)

#print axioms reconstruct_comparison_symmetric
#print axioms comparison_reconstruction_preserves_all_original_answers
#print axioms comparison_reconstruction_recovers_every_symmetric_receipt
#print axioms original_comparison_answers_separate_symmetric_receipts
#print axioms original_comparison_answers_have_unique_symmetric_receipt
end
end AASCMetricConstruction
