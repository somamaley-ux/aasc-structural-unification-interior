import EHKGDiamondHyperbolic
import Mathlib.Topology.Order.MonotoneConvergence

/-! Cauchy crossing for arbitrary continuous future causal curves with no
past or future endpoint in the domain. Repeated parameter values are allowed;
uniqueness concerns the intersection event, not its parameter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem cauchy_map_of_dist_le_scalar {E : Type*} [MetricSpace E]
    (f : ℝ → E) (T : ℝ → ℝ) (l : Filter ℝ) [NeBot l] (L : ℝ)
    (limit : Tendsto T l (𝓝 L)) (control : ∀ s t, dist (f s) (f t) ≤ dist (T s) (T t)) :
    Cauchy (Filter.map f l) := by
  apply Metric.cauchy_iff.mpr
  refine ⟨Filter.map_neBot, ?_⟩
  intro epsilon positive
  let I : Set ℝ := {s | dist (T s) L < epsilon / 2}
  let S : Set E := f '' I
  refine ⟨S, ?_, ?_⟩
  · apply Filter.mem_map.mpr
    have near := (Metric.tendsto_nhds.mp limit) (epsilon / 2) (by positivity)
    filter_upwards [near] with s hs
    exact ⟨s, hs, rfl⟩
  · rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩
    exact (control s t).trans_lt ((dist_triangle (T s) L (T t)).trans_lt (by
      rw [dist_comm L (T t)]
      dsimp [I] at hs ht
      linarith))

theorem causal_curve_space_distance_control (gamma : ℝ → CoordinatePoint)
    (future : ∀ s t, s ≤ t → flatFutureOrder (gamma s) (gamma t)) (s t : ℝ) :
    dist (coordinateSpatialCLM (gamma s)) (coordinateSpatialCLM (gamma t)) ≤
      dist (gamma s 0) (gamma t 0) := by
  rcases le_total s t with order | order
  · have cone := future s t order
    have time := flat_future_time cone
    change ‖coordinateSpatialCLM (gamma t) - coordinateSpatialCLM (gamma s)‖ ≤ gamma t 0 - gamma s 0 at cone
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr time), neg_sub]
    simpa only [norm_sub_rev] using cone
  · have cone := future t s order
    have time := flat_future_time cone
    change ‖coordinateSpatialCLM (gamma s) - coordinateSpatialCLM (gamma t)‖ ≤ gamma s 0 - gamma t 0 at cone
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr time)] using cone

theorem causal_curve_time_bounds (nu : ℝ) (gamma : ℝ → CoordinatePoint)
    (inside : ∀ s, gamma s ∈ protectedDiamond nu) :
    BddBelow (range (fun s => gamma s 0)) ∧ BddAbove (range (fun s => gamma s 0)) := by
  have bound (s : ℝ) : |gamma s 0| < protectedRadius nu :=
    (le_add_of_nonneg_right (norm_nonneg ((coordinateSpatialSplit (gamma s)).2))).trans_lt (inside s)
  exact ⟨⟨-protectedRadius nu, by rintro _ ⟨s, rfl⟩; exact (abs_lt.mp (bound s)).1.le⟩,
    ⟨protectedRadius nu, by rintro _ ⟨s, rfl⟩; exact (abs_lt.mp (bound s)).2.le⟩⟩

theorem causal_curve_ambient_past_endpoint (nu : ℝ) (gamma : ℝ → CoordinatePoint)
    (inside : ∀ s, gamma s ∈ protectedDiamond nu)
    (future : ∀ s t, s ≤ t → flatFutureOrder (gamma s) (gamma t)) :
    ∃ p : CoordinatePoint, Tendsto gamma atBot (𝓝 p) := by
  have mono : Monotone (fun s => gamma s 0) := fun s t h => flat_future_time (future s t h)
  have limit := tendsto_atBot_ciInf mono (causal_curve_time_bounds nu gamma inside).1
  have cauchy := cauchy_map_of_dist_le_scalar (fun s => coordinateSpatialCLM (gamma s))
    (fun s => gamma s 0) atBot _ limit (causal_curve_space_distance_control gamma future)
  obtain ⟨x, spatialLimit⟩ := cauchy_map_iff_exists_tendsto.mp cauchy
  refine ⟨coordinateSpatialSplit.symm (⨅ s, gamma s 0, x), ?_⟩
  have combined := (coordinateSpatialSplit.symm.continuous.tendsto (⨅ s, gamma s 0, x)).comp
    (limit.prodMk_nhds spatialLimit)
  convert combined using 1
  funext s
  exact (coordinateSpatialSplit.symm_apply_apply (gamma s)).symm

theorem causal_curve_ambient_future_endpoint (nu : ℝ) (gamma : ℝ → CoordinatePoint)
    (inside : ∀ s, gamma s ∈ protectedDiamond nu)
    (future : ∀ s t, s ≤ t → flatFutureOrder (gamma s) (gamma t)) :
    ∃ p : CoordinatePoint, Tendsto gamma atTop (𝓝 p) := by
  have mono : Monotone (fun s => gamma s 0) := fun s t h => flat_future_time (future s t h)
  have limit := tendsto_atTop_ciSup mono (causal_curve_time_bounds nu gamma inside).2
  have cauchy := cauchy_map_of_dist_le_scalar (fun s => coordinateSpatialCLM (gamma s))
    (fun s => gamma s 0) atTop _ limit (causal_curve_space_distance_control gamma future)
  obtain ⟨x, spatialLimit⟩ := cauchy_map_iff_exists_tendsto.mp cauchy
  refine ⟨coordinateSpatialSplit.symm (⨆ s, gamma s 0, x), ?_⟩
  have combined := (coordinateSpatialSplit.symm.continuous.tendsto (⨆ s, gamma s 0, x)).comp
    (limit.prodMk_nhds spatialLimit)
  convert combined using 1
  funext s
  exact (coordinateSpatialSplit.symm_apply_apply (gamma s)).symm

theorem past_endpoint_inside_if_nonnegative_time (nu : ℝ) (gamma : ℝ → CoordinatePoint)
    (inside : ∀ s, gamma s ∈ protectedDiamond nu)
    (future : ∀ s t, s ≤ t → flatFutureOrder (gamma s) (gamma t))
    (positive : ∀ s, 0 ≤ gamma s 0) :
    ∃ p ∈ protectedDiamond nu, Tendsto gamma atBot (𝓝 p) := by
  obtain ⟨p, limit⟩ := causal_curve_ambient_past_endpoint nu gamma inside future
  refine ⟨p, ?_, limit⟩
  have bound : diamondGauge p ≤ diamondGauge (gamma 0) := by
    apply le_of_tendsto (diamond_gauge_continuous.tendsto p |>.comp limit)
    apply eventually_atBot.mpr
    refine ⟨0, fun s hs => ?_⟩
    have cone := future s 0 hs
    have triangle := norm_add_le (coordinateSpatialCLM (gamma s) - coordinateSpatialCLM (gamma 0))
      (coordinateSpatialCLM (gamma 0))
    rw [sub_add_cancel] at triangle
    have reversed : ‖coordinateSpatialCLM (gamma s) - coordinateSpatialCLM (gamma 0)‖ ≤ gamma 0 0 - gamma s 0 := by
      change ‖coordinateSpatialCLM (gamma 0) - coordinateSpatialCLM (gamma s)‖ ≤ gamma 0 0 - gamma s 0 at cone
      simpa only [norm_sub_rev] using cone
    dsimp [diamondGauge]
    rw [abs_of_nonneg (positive s), abs_of_nonneg (positive 0)]
    change gamma s 0 + ‖coordinateSpatialCLM (gamma s)‖ ≤ gamma 0 0 + ‖coordinateSpatialCLM (gamma 0)‖
    linarith
  exact bound.trans_lt (inside 0)

theorem future_endpoint_inside_if_nonpositive_time (nu : ℝ) (gamma : ℝ → CoordinatePoint)
    (inside : ∀ s, gamma s ∈ protectedDiamond nu)
    (future : ∀ s t, s ≤ t → flatFutureOrder (gamma s) (gamma t))
    (negative : ∀ s, gamma s 0 ≤ 0) :
    ∃ p ∈ protectedDiamond nu, Tendsto gamma atTop (𝓝 p) := by
  obtain ⟨p, limit⟩ := causal_curve_ambient_future_endpoint nu gamma inside future
  refine ⟨p, ?_, limit⟩
  have bound : diamondGauge p ≤ diamondGauge (gamma 0) := by
    apply le_of_tendsto (diamond_gauge_continuous.tendsto p |>.comp limit)
    apply eventually_atTop.mpr
    refine ⟨0, fun s hs => ?_⟩
    have cone := future 0 s hs
    have triangle := norm_add_le (coordinateSpatialCLM (gamma s) - coordinateSpatialCLM (gamma 0))
      (coordinateSpatialCLM (gamma 0))
    rw [sub_add_cancel] at triangle
    dsimp [flatFutureOrder] at cone
    dsimp [diamondGauge]
    rw [abs_of_nonpos (negative s), abs_of_nonpos (negative 0)]
    change -gamma s 0 + ‖coordinateSpatialCLM (gamma s)‖ ≤ -gamma 0 0 + ‖coordinateSpatialCLM (gamma 0)‖
    change ‖coordinateSpatialCLM (gamma s) - coordinateSpatialCLM (gamma 0)‖ ≤ gamma s 0 - gamma 0 0 at cone
    linarith
  exact bound.trans_lt (inside 0)

structure InextendibleEHFutureCurve (nu : ℝ) (D : Set CoordinatePoint) where
  path : ℝ → CoordinatePoint
  continuous : Continuous path
  inside : ∀ s, path s ∈ D
  future : ∀ s t, s ≤ t → EHMetricFuture nu D (path s) (path t)
  noPastEndpoint : ¬ ∃ p ∈ D, Tendsto path atBot (𝓝 p)
  noFutureEndpoint : ¬ ∃ p ∈ D, Tendsto path atTop (𝓝 p)

theorem central_leaf_cauchy_crossing (nu : ℝ)
    (curve : InextendibleEHFutureCurve nu (protectedDiamond nu)) :
    ∃! p : CoordinatePoint, p ∈ range curve.path ∧ p 0 = 0 := by
  have order : ∀ s t, s ≤ t → flatFutureOrder (curve.path s) (curve.path t) :=
    fun s t h => metric_future_implies_flat (curve.future s t h)
  have past : ∃ s, curve.path s 0 < 0 := by
    by_contra absent
    push_neg at absent
    exact curve.noPastEndpoint (past_endpoint_inside_if_nonnegative_time nu curve.path curve.inside order absent)
  have future : ∃ t, 0 < curve.path t 0 := by
    by_contra absent
    push_neg at absent
    exact curve.noFutureEndpoint (future_endpoint_inside_if_nonpositive_time nu curve.path curve.inside order absent)
  obtain ⟨s, negative⟩ := past
  obtain ⟨t, positive⟩ := future
  have st : s ≤ t := by
    by_contra h
    have bound := flat_future_time (order t s (le_of_not_ge h))
    linarith
  have temporalContinuous : Continuous (fun r => curve.path r 0) := (continuous_apply (0 : Fin 4)).comp curve.continuous
  obtain ⟨r, hr, zero⟩ := intermediate_value_Icc st temporalContinuous.continuousOn ⟨negative.le, positive.le⟩
  refine ⟨curve.path r, ⟨⟨r, rfl⟩, zero⟩, ?_⟩
  rintro q ⟨⟨v, rfl⟩, zeroV⟩
  have spaces (u v : ℝ) (hu : curve.path u 0 = 0) (hv : curve.path v 0 = 0) (uv : u ≤ v) :
      curve.path u = curve.path v := by
    have cone := order u v uv
    have spatial : (coordinateSpatialSplit (curve.path v)).2 = (coordinateSpatialSplit (curve.path u)).2 := by
      apply eq_of_sub_eq_zero
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [flatFutureOrder, hu, hv, sub_self] using cone
    apply coordinateSpatialSplit.injective
    exact Prod.ext (by simpa only [coordinate_split_time, hu, hv]) spatial.symm
  rcases le_total v r with vr | rv
  · exact spaces v r zeroV zero vr
  · exact (spaces r v zero zeroV rv).symm

end AASCKleinGordon.CurvedKG
