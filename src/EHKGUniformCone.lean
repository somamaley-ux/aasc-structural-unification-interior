import OriginalEHMetricActGeometry
import WickOriginalLorentzMetricDomain

/-! Quantitative pointwise cone control for the actual inherited EH operand.
This is geometric preparation for the source-backed Cauchy contract, not a
global-hyperbolicity or evolution theorem. No propagator or desired endpoint
certificate is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
open AASCSemanticExhaustion TopologicalSpace
namespace AASCKleinGordon.CurvedKG

def coordinateSquare (v : Fin 4 → ℝ) : ℝ := ∑ i, v i ^ 2

theorem four_abs_sum_square_le (v : Fin 4 → ℝ) :
    (∑ i, |v i|) ^ 2 ≤ 4 * coordinateSquare v := by
  simp only [coordinateSquare, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (|v 0| + (|v 1| + (|v 2| + |v 3|))) ^ 2 ≤
    4 * (v 0 ^ 2 + (v 1 ^ 2 + (v 2 ^ 2 + v 3 ^ 2)))
  nlinarith [sq_nonneg (|v 0| - |v 1|), sq_nonneg (|v 0| - |v 2|),
    sq_nonneg (|v 0| - |v 3|), sq_nonneg (|v 1| - |v 2|),
    sq_nonneg (|v 1| - |v 3|), sq_nonneg (|v 2| - |v 3|),
    sq_abs (v 0), sq_abs (v 1), sq_abs (v 2), sq_abs (v 3)]

theorem small_matrix_quadratic_error (A : NativeRealMatrix)
    (small : ∀ i j, |A i j| ≤ (1 : ℝ) / 16) (v : Fin 4 → ℝ) :
    |wickMatrixQuadratic A v| ≤ (1 : ℝ) / 4 * coordinateSquare v := by
  have bound : |wickMatrixQuadratic A v| ≤ (1 : ℝ) / 16 * (∑ i, |v i|) ^ 2 := by
    calc
      |wickMatrixQuadratic A v| ≤ ∑ i, |∑ j, v i * A i j * v j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |v i| * ((1 : ℝ) / 16) * |v j| := by
        apply Finset.sum_le_sum
        intro i _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        simp only [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (small i j) (abs_nonneg _)) (abs_nonneg _)
      _ = (1 : ℝ) / 16 * (∑ i, |v i|) ^ 2 := by
        simp only [Finset.sum_mul, Finset.mul_sum, pow_two]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  have cs := four_abs_sum_square_le v
  linarith

theorem coordinate_square_split (v : Fin 4 → ℝ) :
    coordinateSquare v = (v 0) ^ 2 + wickSpatialSquare (Fin.tail v) := by
  simp only [coordinateSquare, wickSpatialSquare, Fin.sum_univ_succ]
  rfl

theorem flat_quadratic_value (v : Fin 4 → ℝ) :
    wickMatrixQuadratic metric v = -(v 0) ^ 2 + wickSpatialSquare (Fin.tail v) := by
  simp [wickMatrixQuadratic, metric, Matrix.diagonal_apply, wickSpatialSquare,
    Fin.sum_univ_succ, Fin.tail, pow_two]

theorem actual_eh_quadratic_split {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (p : CoordinatePoint) (v : Fin 4 → ℝ) :
    wickMatrixQuadratic (originalEHActMetric H p) v =
      -(v 0) ^ 2 + wickSpatialSquare (Fin.tail v) +
        wickMatrixQuadratic (tensorEncode (H p)) v := by
  have metric_eq (i j : Fin 4) : originalEHActMetric H p i j =
      metric i j + tensorEncode (H p) i j := by
    change wickNativeFlatMetric p i j + tensorEncode (H p) i j = _
    rw [original_eh_native_flat_value]
  have split : wickMatrixQuadratic (originalEHActMetric H p) v =
      wickMatrixQuadratic metric v + wickMatrixQuadratic (tensorEncode (H p)) v := by
    simp only [wickMatrixQuadratic, metric_eq, mul_add, add_mul,
      Finset.sum_add_distrib]
  rw [split, flat_quadratic_value]

theorem actual_eh_quadratic_bounds {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (p : CoordinatePoint) (v : Fin 4 → ℝ) :
    (3 : ℝ) / 4 * wickSpatialSquare (Fin.tail v) - (5 : ℝ) / 4 * (v 0) ^ 2 ≤
        wickMatrixQuadratic (originalEHActMetric H p) v ∧
      wickMatrixQuadratic (originalEHActMetric H p) v ≤
        (5 : ℝ) / 4 * wickSpatialSquare (Fin.tail v) - (3 : ℝ) / 4 * (v 0) ^ 2 := by
  have bound := small_matrix_quadratic_error (tensorEncode (H p))
    (fun i j => (original_eh_act_coefficient_bound H inside p i j).le) v
  rw [coordinate_square_split] at bound
  rw [actual_eh_quadratic_split]
  constructor <;> linarith [(abs_le.mp bound).1, (abs_le.mp bound).2]

theorem actual_eh_causal_spatial_bound {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (p : CoordinatePoint) (v : Fin 4 → ℝ)
    (causal : wickMatrixQuadratic (originalEHActMetric H p) v ≤ 0) :
    3 * wickSpatialSquare (Fin.tail v) ≤ 5 * (v 0) ^ 2 := by
  have bound := (actual_eh_quadratic_bounds H inside p v).1
  linarith

theorem actual_eh_nonzero_causal_time {Ω : Opens CoordinatePoint}
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (p : CoordinatePoint) (v : Fin 4 → ℝ) (nonzero : v ≠ 0)
    (causal : wickMatrixQuadratic (originalEHActMetric H p) v ≤ 0) : v 0 ≠ 0 := by
  intro time_zero
  have bound := actual_eh_causal_spatial_bound H inside p v causal
  rw [time_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at bound
  have tail_zero : Fin.tail v = 0 := by
    by_contra tail_nonzero
    have positive := wick_spatial_square_pos (Fin.tail v) tail_nonzero
    linarith
  apply nonzero
  funext i
  refine Fin.cases time_zero (fun j => ?_) i
  exact congrFun tail_zero j

end AASCKleinGordon.CurvedKG
