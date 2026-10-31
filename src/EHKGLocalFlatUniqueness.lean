import EHKGScalarEnergyBalance

/-! Local uniqueness uses arbitrary smooth fields on the open diamond.
An actual compact smooth localization permits the finite-window energy proof;
global homogeneous KG, Schwartz behavior and chosen solution families are not
assumptions. This module first proves the future half of the zero-data result. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem local_flat_future_zero (nu mu : ℝ) (mass : mu ≠ 0) (F : CoordinatePoint → ℝ)
    (regular : ContDiffOn ℝ (⊤ : ℕ∞) F (protectedDiamond nu))
    (equation : ∀ q ∈ protectedDiamond nu, flatScalarResidual (mu ^ 2) F q = 0)
    (position : ∀ x ∈ centralLeafDomain nu, F (centralLeafPoint x) = 0)
    (velocity : ∀ x ∈ centralLeafDomain nu, scalarPartial F (centralLeafPoint x) 0 = 0)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond nu) (future : 0 ≤ p 0) : F p = 0 := by
  obtain ⟨outerR, radius, margin, terminal⟩ := exists_compact_tube_around_future_point nu p inside future
  let center := coordinateSpatialCLM p
  let K := compactCausalTube outerR (p 0) center
  have compactK : IsCompact K := compact_causal_tube_compact _ _ _
  have subsetD : K ⊆ protectedDiamond nu := compact_causal_tube_inside_diamond nu outerR (p 0) center margin
  obtain ⟨G, smoothG, compactG, near⟩ := exists_global_compact_smooth_localization K (protectedDiamond nu)
    compactK (protected_diamond_open nu) subsetD F regular
  let R := (p 0 + outerR) / 2
  have innerRadius : p 0 < R := by dsimp [R]; linarith
  have strictRadius : R < outerR := by dsimp [R]; linarith
  have initialPoint (x : KGSpatialSpace) (hx : x ∈ Metric.closedBall center outerR) : centralLeafPoint x ∈ K :=
    compact_tube_initial_ball outerR (p 0) center x future hx
  have initialZero (x : KGSpatialSpace) (hx : x ∈ Metric.closedBall center outerR) : G (centralLeafPoint x) = 0 := by
    have inK := initialPoint x hx
    rw [(near _ inK).eq_of_nhds]
    exact position x ((central_leaf_in_diamond_iff nu x).mp (subsetD inK))
  have energyZero : G (spaceTimePoint (p 0) center) = 0 := by
    apply smooth_scalar_window_vanishes G smoothG mu R (p 0) center mass future innerRadius
    · intro q hq
      have inK : q ∈ K := ⟨hq.1, hq.2.trans (by linarith)⟩
      rw [flat_residual_congr_of_eventuallyEq _ G F q (near q inK)]
      exact equation q (subsetD inK)
    · intro x hx
      have hxOuter : x ∈ Metric.ball center outerR := by
        have bound : dist x center ≤ R := hx
        exact bound.trans_lt strictRadius
      have hxClosed : x ∈ Metric.closedBall center outerR :=
        (show dist x center < outerR from hxOuter).le
      have inK := initialPoint x hxClosed
      refine ⟨initialZero x hxClosed, ?_, ?_⟩
      · have equal := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single (0 : Fin 4) (1 : ℝ)))
          (near (centralLeafPoint x) inK).fderiv_eq
        change scalarPartial G (centralLeafPoint x) 0 = _ at equal
        change scalarPartial G (centralLeafPoint x) 0 = 0
        rw [equal]
        exact velocity x ((central_leaf_in_diamond_iff nu x).mp (subsetD inK))
      · intro i
        have traceNear : (fun y => G (centralLeafPoint y)) =ᶠ[𝓝 x] (fun _ => 0) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hxOuter] with y hy
          exact initialZero y (show dist y center ≤ outerR from (show dist y center < outerR from hy).le)
        change scalarPartial G (spaceTimePoint 0 x) i.succ = 0
        rw [← scalar_join_spatial_partial G smoothG 0 x i]
        have derivativeZero := traceNear.fderiv_eq (𝕜 := ℝ)
        change fderiv ℝ (fun y => G (spaceTimePoint 0 y)) x = _ at derivativeZero
        rw [derivativeZero]
        simp
  have joinPoint : spaceTimePoint (p 0) center = p := coordinateSpatialSplit.symm_apply_apply p
  rw [joinPoint] at energyZero
  exact ((near p terminal).eq_of_nhds.symm).trans energyZero

end AASCKleinGordon.CurvedKG
