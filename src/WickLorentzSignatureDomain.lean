import WickCompactCurveProtocols
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Actual one-negative/three-positive signature near the original flat matrix.
The domain is specified by coefficient inequalities, before any action output. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickSpatialBlock (G : NativeRealMatrix) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => G i.succ j.succ

def wickSpatialSquare (x : Fin 3 → ℝ) : ℝ := ∑ i, x i ^ 2

theorem wick_spatial_abs_sum_sq_le (x : Fin 3 → ℝ) :
    (∑ i, |x i|)^2 ≤ 3 * wickSpatialSquare x := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, add_zero, wickSpatialSquare]
  nlinarith [sq_nonneg (|x 0|-|x 1|),sq_nonneg (|x 0|-|x 2|),
    sq_nonneg (|x 1|-|x 2|),sq_abs (x 0),sq_abs (x 1),sq_abs (x 2)]

theorem wick_spatial_square_pos (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < wickSpatialSquare x := by
  have hn : ∀ i,0 ≤ x i ^ 2 := fun i => sq_nonneg _
  have he : ∃ i,x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i,hi⟩ := he
  exact Finset.sum_pos' (fun j _ => hn j) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

theorem wick_small_spatial_error (A : Matrix (Fin 3) (Fin 3) ℝ)
    (small : ∀ i j, |A i j| ≤ (1:ℝ)/16) (x : Fin 3 → ℝ) :
    |∑ i,∑ j,x i * A i j * x j| ≤ (1:ℝ)/16 * (∑ i, |x i|)^2 := by
  calc
    |∑ i,∑ j,x i*A i j*x j| ≤ ∑ i,|∑ j,x i*A i j*x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,∑ j,|x i| * ((1:ℝ)/16) * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (small i j) (abs_nonneg _)) (abs_nonneg _)
    _ = (1:ℝ)/16 * (∑ i,|x i|)^2 := by
      simp only [Finset.sum_mul,Finset.mul_sum,pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem wick_small_spatial_block_pos (A : Matrix (Fin 3) (Fin 3) ℝ)
    (small : ∀ i j, |A i j| ≤ (1:ℝ)/16) (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < ∑ i,∑ j,x i * ((1 : Matrix (Fin 3) (Fin 3) ℝ)+A) i j * x j := by
  have hbound := wick_small_spatial_error A small x
  have hcs := wick_spatial_abs_sum_sq_le x
  have hpos := wick_spatial_square_pos x hx
  have hsplit : (∑ i,∑ j,x i*((1 : Matrix (Fin 3) (Fin 3) ℝ)+A) i j*x j) =
      wickSpatialSquare x + (∑ i,∑ j,x i*A i j*x j) := by
    simp [Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib,
      Matrix.one_apply,wickSpatialSquare,pow_two]
  rw [hsplit]
  have hlo := (abs_le.mp hbound).1
  nlinarith

end AASCKleinGordon
