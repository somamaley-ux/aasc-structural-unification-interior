import EHKGDiamondDomain
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Relational preparation for the actual causal curves. The order below is
an auxiliary coordinate order, not a definition of the metric causal relation.
The subsequent curve bridge must prove their equality. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def flatFutureOrder (p q : CoordinatePoint) : Prop :=
  ‖(coordinateSpatialSplit q).2 - (coordinateSpatialSplit p).2‖ ≤ q 0 - p 0

theorem flat_future_refl (p : CoordinatePoint) : flatFutureOrder p p := by
  simp [flatFutureOrder]

theorem flat_future_time {p q : CoordinatePoint} (h : flatFutureOrder p q) : p 0 ≤ q 0 := by
  have positive := norm_nonneg ((coordinateSpatialSplit q).2 - (coordinateSpatialSplit p).2)
  dsimp [flatFutureOrder] at h
  linarith

theorem flat_future_trans {p q z : CoordinatePoint} (hpq : flatFutureOrder p q)
    (hqz : flatFutureOrder q z) : flatFutureOrder p z := by
  have triangle := norm_add_le ((coordinateSpatialSplit z).2 - (coordinateSpatialSplit q).2)
    ((coordinateSpatialSplit q).2 - (coordinateSpatialSplit p).2)
  rw [sub_add_sub_cancel] at triangle
  exact triangle.trans (by dsimp [flatFutureOrder] at *; linarith)

theorem flat_future_antisymm {p q : CoordinatePoint} (hpq : flatFutureOrder p q)
    (hqp : flatFutureOrder q p) : p = q := by
  have time : p 0 = q 0 := le_antisymm (flat_future_time hpq) (flat_future_time hqp)
  have space : (coordinateSpatialSplit p).2 = (coordinateSpatialSplit q).2 := by
    apply eq_of_sub_eq_zero
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [flatFutureOrder, time, sub_self] using hqp
  apply coordinateSpatialSplit.injective
  exact Prod.ext time space

theorem diamond_gauge_order_interval_bound {p q z : CoordinatePoint}
    (hpz : flatFutureOrder p z) (hzq : flatFutureOrder z q) :
    diamondGauge z ≤ max (diamondGauge p) (diamondGauge q) := by
  by_cases sign : 0 ≤ z 0
  · have triangle := norm_add_le ((coordinateSpatialSplit z).2 - (coordinateSpatialSplit q).2)
      (coordinateSpatialSplit q).2
    rw [sub_add_cancel] at triangle
    have reversed : ‖(coordinateSpatialSplit z).2 - (coordinateSpatialSplit q).2‖ ≤ q 0 - z 0 := by
      simpa only [norm_sub_rev] using hzq
    have absq := le_abs_self (q 0)
    have bound : diamondGauge z ≤ diamondGauge q := by
      dsimp [diamondGauge]
      rw [abs_of_nonneg sign]
      linarith
    exact bound.trans (le_max_right _ _)
  · have triangle := norm_add_le ((coordinateSpatialSplit z).2 - (coordinateSpatialSplit p).2)
      (coordinateSpatialSplit p).2
    rw [sub_add_cancel] at triangle
    have absp := neg_le_abs (p 0)
    have bound : diamondGauge z ≤ diamondGauge p := by
      dsimp [diamondGauge]
      rw [abs_of_nonpos (le_of_not_ge sign)]
      dsimp [flatFutureOrder] at hpz
      linarith
    exact bound.trans (le_max_left _ _)

theorem protected_diamond_order_convex (nu : ℝ) {p q z : CoordinatePoint}
    (hp : p ∈ protectedDiamond nu) (hq : q ∈ protectedDiamond nu)
    (hpz : flatFutureOrder p z) (hzq : flatFutureOrder z q) : z ∈ protectedDiamond nu :=
  (diamond_gauge_order_interval_bound hpz hzq).trans_lt (max_lt hp hq)

theorem flat_future_closed_left (p : CoordinatePoint) : IsClosed {q | flatFutureOrder p q} := by
  exact isClosed_le ((continuous_snd.comp coordinateSpatialSplit.continuous).sub continuous_const).norm
    ((continuous_apply (0 : Fin 4)).sub continuous_const)

theorem flat_future_closed_right (q : CoordinatePoint) : IsClosed {p | flatFutureOrder p q} := by
  exact isClosed_le (continuous_const.sub (continuous_snd.comp coordinateSpatialSplit.continuous)).norm
    (continuous_const.sub (continuous_apply (0 : Fin 4)))

theorem flat_order_interval_compact (nu : ℝ) (p q : CoordinatePoint)
    (hp : p ∈ protectedDiamond nu) (hq : q ∈ protectedDiamond nu) :
    IsCompact {z | flatFutureOrder p z ∧ flatFutureOrder z q} := by
  apply (isCompact_closedBall (0 : CoordinatePoint) (protectedRadius nu)).of_isClosed_subset
    ((flat_future_closed_left p).inter (flat_future_closed_right q))
  intro z hz
  change dist z 0 ≤ protectedRadius nu
  rw [dist_zero_right]
  exact (coordinate_norm_le_diamond_gauge z).trans
    ((diamond_gauge_order_interval_bound hz.1 hz.2).trans (le_of_lt (max_lt hp hq)))

theorem flat_spatial_square_eq_norm (v : CoordinatePoint) :
    wickSpatialSquare (Fin.tail v) = ‖(coordinateSpatialSplit v).2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, wickSpatialSquare]
  change (∑ i : Fin 3, v i.succ ^ 2) = ∑ i : Fin 3, v i.succ * v i.succ
  simp only [pow_two]

theorem actual_future_tangent_iff (nu : ℝ) (p v : CoordinatePoint) :
    (wickMatrixQuadratic (originalEHActMetric (conformalOperand nu) p) v ≤ 0 ∧ 0 ≤ v 0) ↔
      ‖(coordinateSpatialSplit v).2‖ ≤ v 0 := by
  rw [conformal_operand_causal_tangent_iff, flat_quadratic_value, flat_spatial_square_eq_norm]
  constructor
  · rintro ⟨causal, future⟩
    nlinarith [norm_nonneg (coordinateSpatialSplit v).2]
  · intro h
    constructor
    · nlinarith [norm_nonneg (coordinateSpatialSplit v).2]
    · exact (norm_nonneg _).trans h

end AASCKleinGordon.CurvedKG
