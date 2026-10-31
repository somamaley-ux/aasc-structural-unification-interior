import EHKGDiamondCauchyLeaf
import KGConcreteSineFinitePropagation
import Mathlib.Topology.Maps.Proper.Basic

/-! Finite propagation of the actual full compact-data construction. The
cosine term is obtained by differentiating the actual locally vanishing sine
family. Its causal shadow uses the same metric's proved curve relation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG

theorem spatial_cosine_vanishes_of_abs_time_lt (a : Parameters) (f : 𝓢(KGSpatialSpace, ℂ))
    (R t : ℝ) (x : KGSpatialSpace) (time : |t| < R)
    (initial : ∀ y ∈ Metric.closedBall x R, f y = 0) : spatialCosineSolutionCLM a t f x = 0 := by
  have near : (fun s : ℝ => spatialSineSolutionCLM a s f x) =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds time] with s hs
    exact spatialSineSolution_vanishes_of_abs_time_lt a f R s x hs initial
  have derivative := (spatialSineSolution_hasDerivAt a f t x).deriv
  rw [near.deriv_eq] at derivative
  simpa only [deriv_const] using derivative.symm

theorem full_flat_vanishes_of_abs_time_lt (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (R t : ℝ) (x : KGSpatialSpace) (time : |t| < R)
    (position : ∀ y ∈ Metric.closedBall x R, f y = 0)
    (velocity : ∀ y ∈ Metric.closedBall x R, h y = 0) : fullFlatPosition a f h t x = 0 := by
  simp only [fullFlatPosition, SchwartzMap.add_apply,
    spatial_cosine_vanishes_of_abs_time_lt a f R t x time position,
    spatialSineSolution_vanishes_of_abs_time_lt a h R t x time velocity, add_zero]

theorem compact_field_vanishes_outside_initial_ball (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (R : ℝ) (p : CoordinatePoint)
    (time : |p 0| < R)
    (position : ∀ y ∈ Metric.closedBall (coordinateSpatialCLM p) R, f y = 0)
    (velocity : ∀ y ∈ Metric.closedBall (coordinateSpatialCLM p) R, h y = 0) :
    compactCurvedField a U f h p = 0 := by
  have flat := full_flat_vanishes_of_abs_time_lt (auxiliaryKGParameters a)
    (compactCauchySchwartzCLM U f) (compactCauchySchwartzCLM U h) R (p 0) (coordinateSpatialCLM p) time
    (fun y hy => by rw [compact_cauchy_schwartz_apply, position y hy]; rfl)
    (fun y hy => by rw [compact_cauchy_schwartz_apply, velocity y hy]; rfl)
  change Real.cos (conformalFrequency a * p 0) * Complex.reCLM
    (fullFlatPosition _ _ _ (p 0) (coordinateSpatialCLM p)) = 0
  rw [flat, map_zero, mul_zero]

theorem compact_field_nonzero_has_causal_initial_point (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint)
    (nonzero : compactCurvedField a U f h p ≠ 0) :
    ∃ y ∈ tsupport f ∪ tsupport h, dist (coordinateSpatialCLM p) y ≤ |p 0| := by
  let K : Set KGSpatialSpace := tsupport f ∪ tsupport h
  have compact : IsCompact K := f.hasCompactSupport.union h.hasCompactSupport
  by_contra absent
  push_neg at absent
  have far (y : KGSpatialSpace) (hy : y ∈ K) : |p 0| < dist (coordinateSpatialCLM p) y := absent y hy
  by_cases inhabited : K.Nonempty
  · have continuousDistance : Continuous (fun y : KGSpatialSpace => dist (coordinateSpatialCLM p) y) :=
      continuous_const.dist continuous_id
    obtain ⟨y, hy, minimal⟩ := compact.exists_isMinOn inhabited continuousDistance.continuousOn
    let R := (|p 0| + dist (coordinateSpatialCLM p) y) / 2
    have time : |p 0| < R := by dsimp [R]; linarith [far y hy]
    have below : R < dist (coordinateSpatialCLM p) y := by dsimp [R]; linarith [far y hy]
    apply nonzero
    apply compact_field_vanishes_outside_initial_ball a U f h R p time
    · intro z hz
      by_contra nz
      have member : z ∈ K := Or.inl (subset_tsupport f (show z ∈ Function.support f from nz))
      have bound : dist (coordinateSpatialCLM p) y ≤ dist (coordinateSpatialCLM p) z := minimal member
      have radius : dist (coordinateSpatialCLM p) z ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hz
      linarith
    · intro z hz
      by_contra nz
      have member : z ∈ K := Or.inr (subset_tsupport h (show z ∈ Function.support h from nz))
      have bound : dist (coordinateSpatialCLM p) y ≤ dist (coordinateSpatialCLM p) z := minimal member
      have radius : dist (coordinateSpatialCLM p) z ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hz
      linarith
  · apply nonzero
    apply compact_field_vanishes_outside_initial_ball a U f h (|p 0| + 1) p (by linarith)
    · intro z hz
      by_contra nz
      exact inhabited ⟨z, Or.inl (subset_tsupport f (show z ∈ Function.support f from nz))⟩
    · intro z hz
      by_contra nz
      exact inhabited ⟨z, Or.inr (subset_tsupport h (show z ∈ Function.support h from nz))⟩

def metricCausalShadow (nu : ℝ) (K : Set KGSpatialSpace) : Set CoordinatePoint :=
  {p | p ∈ protectedDiamond nu ∧ ∃ y ∈ K,
    EHMetricFuture nu (protectedDiamond nu) (centralLeafPoint y) p ∨
      EHMetricFuture nu (protectedDiamond nu) p (centralLeafPoint y)}

theorem compact_curved_support_in_metric_causal_shadow (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    Function.support (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) ∩
      protectedDiamond (conformalFrequency a) ⊆ metricCausalShadow (conformalFrequency a) (tsupport f ∪ tsupport h) := by
  rintro p ⟨nonzero, inside⟩
  obtain ⟨y, hy, distance⟩ := compact_field_nonzero_has_causal_initial_point a _ f h p nonzero
  have leaf : y ∈ centralLeafDomain (conformalFrequency a) := by
    rcases hy with position | velocity
    · exact f.tsupport_subset position
    · exact h.tsupport_subset velocity
  have initialInside := (central_leaf_in_diamond_iff _ y).mpr leaf
  refine ⟨inside, y, hy, ?_⟩
  by_cases sign : 0 ≤ p 0
  · left
    apply (metric_future_iff_flat_on_diamond _ _ _ initialInside inside).mpr
    simpa only [flatFutureOrder, central_leaf_space, central_leaf_time, sub_zero,
      dist_eq_norm, abs_of_nonneg sign] using distance
  · right
    apply (metric_future_iff_flat_on_diamond _ _ _ inside initialInside).mpr
    have negative := le_of_not_ge sign
    simpa only [flatFutureOrder, central_leaf_space, central_leaf_time, zero_sub,
      dist_eq_norm, norm_sub_rev, abs_of_nonpos negative] using distance

def flatInitialCausalShadow (K : Set KGSpatialSpace) : Set CoordinatePoint :=
  {p | ∃ y ∈ K, dist (coordinateSpatialCLM p) y ≤ |p 0|}

theorem flat_initial_causal_shadow_closed (K : Set KGSpatialSpace) (compact : IsCompact K) :
    IsClosed (flatInitialCausalShadow K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let relation : Set (K × CoordinatePoint) :=
    {z | dist (coordinateSpatialCLM z.2) (z.1 : KGSpatialSpace) ≤ |z.2 0|}
  have closedRelation : IsClosed relation := isClosed_le
    ((coordinateSpatialCLM.continuous.comp continuous_snd).dist (continuous_subtype_val.comp continuous_fst))
    (((continuous_apply (0 : Fin 4)).comp continuous_snd).abs)
  have image : Prod.snd '' relation = flatInitialCausalShadow K := by
    ext p
    constructor
    · rintro ⟨⟨y, q⟩, h, rfl⟩
      exact ⟨y, y.property, h⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨(⟨y, hy⟩, p), h, rfl⟩
  rw [← image]
  exact isClosedMap_snd_of_compactSpace relation closedRelation

theorem compact_curved_closed_support_in_metric_causal_shadow (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    tsupport (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) ∩
      protectedDiamond (conformalFrequency a) ⊆ metricCausalShadow (conformalFrequency a) (tsupport f ∪ tsupport h) := by
  have pointwise : Function.support (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) ⊆
      flatInitialCausalShadow (tsupport f ∪ tsupport h) := by
    intro p nonzero
    exact compact_field_nonzero_has_causal_initial_point a _ f h p nonzero
  have closed := flat_initial_causal_shadow_closed (tsupport f ∪ tsupport h)
    (f.hasCompactSupport.union h.hasCompactSupport)
  have closureBound := closure_minimal pointwise closed
  rintro p ⟨supported, inside⟩
  obtain ⟨y, hy, distance⟩ := closureBound supported
  have leaf : y ∈ centralLeafDomain (conformalFrequency a) := by
    rcases hy with position | velocity
    · exact f.tsupport_subset position
    · exact h.tsupport_subset velocity
  have initialInside := (central_leaf_in_diamond_iff _ y).mpr leaf
  refine ⟨inside, y, hy, ?_⟩
  by_cases sign : 0 ≤ p 0
  · left
    apply (metric_future_iff_flat_on_diamond _ _ _ initialInside inside).mpr
    simpa only [flatFutureOrder, central_leaf_space, central_leaf_time, sub_zero,
      dist_eq_norm, abs_of_nonneg sign] using distance
  · right
    apply (metric_future_iff_flat_on_diamond _ _ _ inside initialInside).mpr
    have negative := le_of_not_ge sign
    simpa only [flatFutureOrder, central_leaf_space, central_leaf_time, zero_sub,
      dist_eq_norm, norm_sub_rev, abs_of_nonpos negative] using distance

end AASCKleinGordon.CurvedKG
