import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Semantic invariant-tensor subproblem for Einstein Dynamics Lemma 21.5.
The candidate is an arbitrary real rank-two array. Its only hypothesis is
invariance under every actual invertible comparison preserving the received
Lorentz form. No expression datatype, assumed normal form, Euclidean rotation
group, or completeness certificate occurs.

This is the fixed four-dimensional Lorentzian fibre of the manuscript's
declared metric-projection envelope. It does not construct that physical metric
from the Kernel, prove a natural-operator jet theorem, or classify curvature
response operators. Those obligations remain distinct.
-/

namespace AASCSemanticExhaustion

open scoped Matrix

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.vecHead Matrix.vecTail
  Matrix.transpose_apply Matrix.diagonal_apply

abbrev Tensor2 := Matrix (Fin 4) (Fin 4) ℝ

def metric : Tensor2 := Matrix.diagonal ![-1, 1, 1, 1]

structure LorentzComparison where
  forward : Tensor2
  inverse : Tensor2
  left_inverse : inverse * forward = 1
  right_inverse : forward * inverse = 1
  metric_preserved : forward.transpose * metric * forward = metric

/-- Independent semantic predicate on arbitrary rank-two tensor values. -/
def InvariantBaseline (B : Tensor2) : Prop :=
  ∀ L : LorentzComparison, L.forward.transpose * B * L.forward = B

theorem metric_is_invariant : InvariantBaseline metric :=
  fun L => L.metric_preserved

def flipMatrix (k : Fin 4) : Tensor2 :=
  Matrix.diagonal (fun i => if i = k then -1 else 1)

def flipComparison (k : Fin 4) : LorentzComparison where
  forward := flipMatrix k
  inverse := flipMatrix k
  left_inverse := by
    ext i j
    by_cases h : i = j
    · subst j
      by_cases hi : i = k <;>
        simp [flipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, hi]
    · simp [flipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  right_inverse := by
    ext i j
    by_cases h : i = j
    · subst j
      by_cases hi : i = k <;>
        simp [flipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, hi]
    · simp [flipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, h]
  metric_preserved := by
    ext i j
    by_cases h : i = j
    · subst j
      by_cases hi : i = k <;>
        simp [flipMatrix, metric, Matrix.diagonal_mul, Matrix.mul_diagonal, hi]
    · simp [flipMatrix, metric, Matrix.diagonal_mul, Matrix.mul_diagonal, h]

theorem invariant_baseline_off_diagonal (B : Tensor2)
    (hB : InvariantBaseline B) (i j : Fin 4) (hij : i ≠ j) : B i j = 0 := by
  have h := congrArg (fun M : Tensor2 => M i j) (hB (flipComparison i))
  simp [flipComparison, flipMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
    hij, Ne.symm hij] at h
  linarith

def swap12Matrix : Tensor2 :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

def swap13Matrix : Tensor2 :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]

def swap12Comparison : LorentzComparison where
  forward := swap12Matrix
  inverse := swap12Matrix
  left_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swap12Matrix, Matrix.mul_apply, Fin.sum_univ_four]
  right_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swap12Matrix, Matrix.mul_apply, Fin.sum_univ_four]
  metric_preserved := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swap12Matrix, metric, Matrix.mul_apply, Fin.sum_univ_four]

def swap13Comparison : LorentzComparison where
  forward := swap13Matrix
  inverse := swap13Matrix
  left_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swap13Matrix, Matrix.mul_apply, Fin.sum_univ_four]
  right_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swap13Matrix, Matrix.mul_apply, Fin.sum_univ_four]
  metric_preserved := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [swap13Matrix, metric, Matrix.mul_apply, Fin.sum_univ_four]

noncomputable def boostMatrix : Tensor2 :=
  !![5/4, 3/4, 0, 0; 3/4, 5/4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

noncomputable def boostInverseMatrix : Tensor2 :=
  !![5/4, -3/4, 0, 0; -3/4, 5/4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

noncomputable def boostComparison : LorentzComparison where
  forward := boostMatrix
  inverse := boostInverseMatrix
  left_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [boostMatrix, boostInverseMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  right_inverse := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [boostMatrix, boostInverseMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  metric_preserved := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [boostMatrix, metric, Matrix.mul_apply, Fin.sum_univ_four]

theorem invariant_baseline_spatial_diagonals (B : Tensor2)
    (hB : InvariantBaseline B) : B 2 2 = B 1 1 ∧ B 3 3 = B 1 1 := by
  constructor
  · have h := congrArg (fun M : Tensor2 => M 1 1) (hB swap12Comparison)
    simpa [swap12Comparison, swap12Matrix, Matrix.mul_apply, Fin.sum_univ_four] using h
  · have h := congrArg (fun M : Tensor2 => M 1 1) (hB swap13Comparison)
    simpa [swap13Comparison, swap13Matrix, Matrix.mul_apply, Fin.sum_univ_four] using h

theorem invariant_baseline_time_diagonal (B : Tensor2)
    (hB : InvariantBaseline B) : B 0 0 = -B 1 1 := by
  have h := congrArg (fun M : Tensor2 => M 0 0) (hB boostComparison)
  have h01 := invariant_baseline_off_diagonal B hB 0 1 (by decide)
  have h10 := invariant_baseline_off_diagonal B hB 1 0 (by decide)
  norm_num [boostComparison, boostMatrix, Matrix.mul_apply, Fin.sum_univ_four,
    h01, h10] at h
  linarith

/-- Semantic completeness for the zero-curvature rank-two fibre. Invariance
forces the metric baseline; the candidate class is not defined as metric multiples. -/
theorem invariant_baseline_unique_metric_multiple (B : Tensor2)
    (hB : InvariantBaseline B) : ∃! c : ℝ, B = c • metric := by
  have hspace := invariant_baseline_spatial_diagonals B hB
  have htime := invariant_baseline_time_diagonal B hB
  refine ⟨B 1 1, ?_, ?_⟩
  · ext i j
    by_cases h : i = j
    · subst j
      fin_cases i <;> simp [metric, htime, hspace.1, hspace.2]
    · simpa [metric, Matrix.diagonal_apply, h] using
        invariant_baseline_off_diagonal B hB i j h
  · intro c hc
    have h := congrArg (fun M : Tensor2 => M 1 1) hc
    simpa [metric] using h.symm

theorem invariant_baseline_iff_metric_multiple (B : Tensor2) :
    InvariantBaseline B ↔ ∃ c : ℝ, B = c • metric := by
  constructor
  · intro h
    obtain ⟨c, hc, _⟩ := invariant_baseline_unique_metric_multiple B h
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    intro L
    rw [Matrix.mul_smul, Matrix.smul_mul, L.metric_preserved]

#print axioms metric_is_invariant
#print axioms invariant_baseline_off_diagonal
#print axioms invariant_baseline_spatial_diagonals
#print axioms invariant_baseline_time_diagonal
#print axioms invariant_baseline_unique_metric_multiple
#print axioms invariant_baseline_iff_metric_multiple

end AASCSemanticExhaustion
