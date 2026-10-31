import EHKGCompactSmoothLocalization

/-! Compact shrinking tubes strictly inside the same EH diamond. They are
the actual compact sets used to localize arbitrary local comparison fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def compactCausalTube (R T : ℝ) (center : KGSpatialSpace) : Set CoordinatePoint :=
  {p | p 0 ∈ Icc 0 T ∧ ‖coordinateSpatialCLM p - center‖ ≤ R - p 0}

theorem compact_causal_tube_closed (R T : ℝ) (center : KGSpatialSpace) :
    IsClosed (compactCausalTube R T center) :=
  ((isClosed_Icc.preimage (continuous_apply (0 : Fin 4))).inter
    (isClosed_le (coordinateSpatialCLM.continuous.sub continuous_const).norm
      (continuous_const.sub (continuous_apply (0 : Fin 4)))))

theorem compact_causal_tube_gauge_bound (R T : ℝ) (center : KGSpatialSpace)
    (p : CoordinatePoint) (inside : p ∈ compactCausalTube R T center) :
    diamondGauge p ≤ R + ‖center‖ := by
  have triangle := norm_add_le (coordinateSpatialCLM p - center) center
  rw [sub_add_cancel] at triangle
  change |p 0| + ‖coordinateSpatialCLM p‖ ≤ R + ‖center‖
  rw [abs_of_nonneg inside.1.1]
  linarith [inside.2]

theorem compact_causal_tube_compact (R T : ℝ) (center : KGSpatialSpace) :
    IsCompact (compactCausalTube R T center) := by
  apply (isCompact_closedBall (0 : CoordinatePoint) (R + ‖center‖)).of_isClosed_subset
    (compact_causal_tube_closed R T center)
  intro p hp
  change dist p 0 ≤ R + ‖center‖
  rw [dist_zero_right]
  exact (coordinate_norm_le_diamond_gauge p).trans (compact_causal_tube_gauge_bound R T center p hp)

theorem compact_causal_tube_inside_diamond (nu R T : ℝ) (center : KGSpatialSpace)
    (margin : R + ‖center‖ < protectedRadius nu) : compactCausalTube R T center ⊆ protectedDiamond nu := by
  intro p hp
  exact (compact_causal_tube_gauge_bound R T center p hp).trans_lt margin

theorem compact_tube_initial_ball (R T : ℝ) (center x : KGSpatialSpace)
    (time : 0 ≤ T) (inside : x ∈ Metric.closedBall center R) :
    centralLeafPoint x ∈ compactCausalTube R T center := by
  refine ⟨by simpa only [central_leaf_time] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, time⟩), ?_⟩
  change ‖(coordinateSpatialSplit (centralLeafPoint x)).2 - center‖ ≤ R - centralLeafPoint x 0
  rw [central_leaf_space, central_leaf_time, sub_zero]
  simpa only [Metric.mem_closedBall, dist_eq_norm] using inside

theorem compact_tube_terminal_center (R T : ℝ) (center : KGSpatialSpace)
    (time : 0 ≤ T) (radius : T ≤ R) :
    coordinateSpatialSplit.symm (T, center) ∈ compactCausalTube R T center := by
  constructor
  · change T ∈ Icc 0 T
    exact ⟨time, le_rfl⟩
  · change ‖center - center‖ ≤ R - T
    simpa only [sub_self, norm_zero] using sub_nonneg.mpr radius

theorem exists_compact_tube_around_future_point (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) (future : 0 ≤ p 0) :
    ∃ R : ℝ, p 0 < R ∧ R + ‖coordinateSpatialCLM p‖ < protectedRadius nu ∧
      p ∈ compactCausalTube R (p 0) (coordinateSpatialCLM p) := by
  let R := (p 0 + protectedRadius nu - ‖coordinateSpatialCLM p‖) / 2
  have bound : p 0 + ‖coordinateSpatialCLM p‖ < protectedRadius nu := by
    change |p 0| + ‖coordinateSpatialCLM p‖ < protectedRadius nu at inside
    simpa only [abs_of_nonneg future] using inside
  have radius : p 0 < R := by dsimp [R]; linarith
  refine ⟨R, radius, by dsimp [R]; linarith, ?_⟩
  exact ⟨⟨future, le_rfl⟩, by simp only [sub_self, norm_zero]; linarith⟩

end AASCKleinGordon.CurvedKG
