import EHKGMetricCausalCurves

/-! Global hyperbolicity in the standard causal-convex-neighborhood and
compact-causal-diamond criterion, for the explicitly defined piecewise C1
causal relation of the actual EH metric. No Cauchy-evolution premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def EHStronglyCausalOn (nu : ℝ) (D : Set CoordinatePoint) : Prop :=
  ∀ p ∈ D, ∀ U : Set CoordinatePoint, IsOpen U → p ∈ U →
    ∃ V : Set CoordinatePoint, IsOpen V ∧ p ∈ V ∧ V ⊆ D ∩ U ∧
      ∀ x ∈ V, ∀ y ∈ V, ∀ z ∈ D,
        EHMetricFuture nu D x z → EHMetricFuture nu D z y → z ∈ V

def EHGloballyHyperbolicOn (nu : ℝ) (D : Set CoordinatePoint) : Prop :=
  EHStronglyCausalOn nu D ∧ ∀ p ∈ D, ∀ q ∈ D,
    IsCompact {z | z ∈ D ∧ EHMetricFuture nu D p z ∧ EHMetricFuture nu D z q}

theorem flat_future_sub_center (p q c : CoordinatePoint) :
    flatFutureOrder (p - c) (q - c) ↔ flatFutureOrder p q := by
  have spatial : coordinateSpatialCLM (q - c) - coordinateSpatialCLM (p - c) =
      coordinateSpatialCLM q - coordinateSpatialCLM p := by rw [map_sub, map_sub]; abel
  change (‖coordinateSpatialCLM (q - c) - coordinateSpatialCLM (p - c)‖ ≤ (q 0 - c 0) - (p 0 - c 0)) ↔ _
  rw [spatial]
  have time : (q 0 - c 0) - (p 0 - c 0) = q 0 - p 0 := by ring
  rw [time]
  rfl

theorem translated_diamond_order_convex (c : CoordinatePoint) (r : ℝ) {p q z : CoordinatePoint}
    (hp : diamondGauge (p - c) < r) (hq : diamondGauge (q - c) < r)
    (hpz : flatFutureOrder p z) (hzq : flatFutureOrder z q) : diamondGauge (z - c) < r :=
  (diamond_gauge_order_interval_bound ((flat_future_sub_center p z c).mpr hpz)
    ((flat_future_sub_center z q c).mpr hzq)).trans_lt (max_lt hp hq)

theorem protected_diamond_strongly_causal (nu : ℝ) : EHStronglyCausalOn nu (protectedDiamond nu) := by
  intro p hp U openU pU
  obtain ⟨r, positive, contained⟩ := Metric.mem_nhds_iff.mp
    (((protected_diamond_open nu).inter openU).mem_nhds ⟨hp, pU⟩)
  let V : Set CoordinatePoint := {z | diamondGauge (z - p) < r}
  refine ⟨V, isOpen_lt (diamond_gauge_continuous.comp (continuous_id.sub continuous_const)) continuous_const,
    ?_, ?_, ?_⟩
  · simpa [V, diamondGauge] using positive
  · intro z hz
    apply contained
    change dist z p < r
    rw [dist_eq_norm]
    exact (coordinate_norm_le_diamond_gauge (z - p)).trans_lt hz
  · intro x hx y hy z hz past future
    exact translated_diamond_order_convex p r hx hy (metric_future_implies_flat past)
      (metric_future_implies_flat future)

theorem actual_causal_diamond_eq_flat_interval (nu : ℝ) (p q : CoordinatePoint)
    (hp : p ∈ protectedDiamond nu) (hq : q ∈ protectedDiamond nu) :
    {z | z ∈ protectedDiamond nu ∧ EHMetricFuture nu (protectedDiamond nu) p z ∧
      EHMetricFuture nu (protectedDiamond nu) z q} =
      {z | flatFutureOrder p z ∧ flatFutureOrder z q} := by
  ext z
  constructor
  · rintro ⟨hz, past, future⟩
    exact ⟨metric_future_implies_flat past, metric_future_implies_flat future⟩
  · rintro ⟨past, future⟩
    have hz := protected_diamond_order_convex nu hp hq past future
    exact ⟨hz, (metric_future_iff_flat_on_diamond nu p z hp hz).mpr past,
      (metric_future_iff_flat_on_diamond nu z q hz hq).mpr future⟩

theorem protected_diamond_globally_hyperbolic (nu : ℝ) :
    EHGloballyHyperbolicOn nu (protectedDiamond nu) := by
  refine ⟨protected_diamond_strongly_causal nu, ?_⟩
  intro p hp q hq
  rw [actual_causal_diamond_eq_flat_interval nu p q hp hq]
  exact flat_order_interval_compact nu p q hp hq

theorem curved_occupied_globally_hyperbolic_domain (a : Parameters) :
    (0 : CoordinatePoint) ∈ protectedDiamond (conformalFrequency a) ∧
      IsOpen (protectedDiamond (conformalFrequency a)) ∧
      EHGloballyHyperbolicOn (conformalFrequency a) (protectedDiamond (conformalFrequency a)) ∧
      conformalOperand (conformalFrequency a) ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
      loweredConnectionCurvature (originalEHActMetric (conformalOperand (conformalFrequency a)))
        (leviCivitaCoefficients (originalEHActMetric (conformalOperand (conformalFrequency a))))
          0 0 1 0 1 ≠ 0 :=
  ⟨protected_diamond_zero _, protected_diamond_open _, protected_diamond_globally_hyperbolic _,
    (protected_same_eh_nonflat a).2.1, (protected_same_eh_nonflat a).2.2⟩

end AASCKleinGordon.CurvedKG
