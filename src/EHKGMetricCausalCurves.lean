import EHKGDiamondCausalOrder
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Future causal curves use the actual original metric and its tangent
quadratic form. Equality with the auxiliary coordinate order is proved,
rather than using that order as an unverified causal-relation bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def coordinateSpatialCLM : CoordinatePoint →L[ℝ] KGSpatialSpace :=
  (ContinuousLinearMap.snd ℝ ℝ KGSpatialSpace).comp coordinateSpatialSplit.toContinuousLinearMap

theorem diamond_gauge_add_le (p q : CoordinatePoint) :
    diamondGauge (p + q) ≤ diamondGauge p + diamondGauge q := by
  have time := abs_add_le (p 0) (q 0)
  have space := norm_add_le (coordinateSpatialCLM p) (coordinateSpatialCLM q)
  change |p 0 + q 0| + ‖coordinateSpatialCLM (p + q)‖ ≤ _
  rw [map_add]
  dsimp [diamondGauge]
  change |p 0 + q 0| + ‖coordinateSpatialCLM p + coordinateSpatialCLM q‖ ≤
    (|p 0| + ‖coordinateSpatialCLM p‖) + (|q 0| + ‖coordinateSpatialCLM q‖)
  exact add_le_add time space |>.trans (le_of_eq (by ring))

theorem diamond_gauge_smul (r : ℝ) (p : CoordinatePoint) :
    diamondGauge (r • p) = |r| * diamondGauge p := by
  change |r * p 0| + ‖coordinateSpatialCLM (r • p)‖ = _
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_mul]
  dsimp [diamondGauge]
  change |r| * |p 0| + |r| * ‖coordinateSpatialCLM p‖ = |r| * (|p 0| + ‖coordinateSpatialCLM p‖)
  ring

theorem protected_diamond_convex (nu : ℝ) : Convex ℝ (protectedDiamond nu) := by
  intro p hp q hq a b ha hb hab
  have sum := diamond_gauge_add_le (a • p) (b • q)
  rw [diamond_gauge_smul, diamond_gauge_smul, abs_of_nonneg ha, abs_of_nonneg hb] at sum
  change diamondGauge (a • p + b • q) < protectedRadius nu
  have strict : a * diamondGauge p + b * diamondGauge q < protectedRadius nu := by
    by_cases zero : a = 0
    · have bone : b = 1 := by linarith
      simpa [zero, bone] using hq
    · have apos : 0 < a := lt_of_le_of_ne ha (Ne.symm zero)
      have left := mul_lt_mul_of_pos_left hp apos
      have right := mul_le_mul_of_nonneg_left hq.le hb
      have weightedRadius : a * protectedRadius nu + b * protectedRadius nu = protectedRadius nu := by
        rw [← add_mul, hab, one_mul]
      linarith
  exact sum.trans_lt strict

structure EHFutureCausalSegment (nu : ℝ) (D : Set CoordinatePoint) (p q : CoordinatePoint) where
  path : ℝ → CoordinatePoint
  regular : ContDiffOn ℝ 1 path (Icc 0 1)
  initial : path 0 = p
  final : path 1 = q
  inside : MapsTo path (Icc 0 1) D
  future : ∀ s ∈ Ioo (0 : ℝ) 1,
    wickMatrixQuadratic (originalEHActMetric (conformalOperand nu) (path s)) (deriv path s) ≤ 0 ∧
      0 ≤ deriv path s 0

theorem EHFutureCausalSegment.flat_order {nu : ℝ} {D : Set CoordinatePoint}
    {p q : CoordinatePoint} (segment : EHFutureCausalSegment nu D p q) : flatFutureOrder p q := by
  have functional (w : KGSpatialSpace) (hw : ‖w‖ ≤ 1) :
      inner ℝ w ((coordinateSpatialSplit q).2 - (coordinateSpatialSplit p).2) ≤ q 0 - p 0 := by
    let F : ℝ → ℝ := fun s => inner ℝ w (coordinateSpatialCLM (segment.path s)) - segment.path s 0
    have continuousF : ContinuousOn F (Icc 0 1) :=
      (continuousOn_const.inner (coordinateSpatialCLM.continuous.comp_continuousOn segment.regular.continuousOn)).sub
        ((continuous_apply (0 : Fin 4)).comp_continuousOn segment.regular.continuousOn)
    have differentiable (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : DifferentiableAt ℝ segment.path s :=
      (segment.regular.differentiableOn_one s ⟨hs.1.le, hs.2.le⟩).differentiableAt (Icc_mem_nhds hs.1 hs.2)
    have derivative (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
        HasDerivAt F (inner ℝ w (coordinateSpatialCLM (deriv segment.path s)) - deriv segment.path s 0) s := by
      have spatial := coordinateSpatialCLM.hasFDerivAt.comp_hasDerivAt s (differentiable s hs).hasDerivAt
      have temporal := (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s
        (differentiable s hs).hasDerivAt
      simpa only [inner_zero_left, add_zero] using
        (HasDerivAt.inner ℝ (hasDerivAt_const s w) spatial).sub temporal
    have nonpositive (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
        inner ℝ w (coordinateSpatialCLM (deriv segment.path s)) - deriv segment.path s 0 ≤ 0 := by
      have cone := (actual_future_tangent_iff nu (segment.path s) (deriv segment.path s)).mp (segment.future s hs)
      have innerBound := real_inner_le_norm w (coordinateSpatialCLM (deriv segment.path s))
      have productBound := mul_le_mul_of_nonneg_right hw (norm_nonneg (coordinateSpatialCLM (deriv segment.path s)))
      change ‖coordinateSpatialCLM (deriv segment.path s)‖ ≤ deriv segment.path s 0 at cone
      linarith
    have anti : AntitoneOn F (Icc 0 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) continuousF
        (fun s hs => (derivative s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt)
        (fun s hs => nonpositive s (by simpa only [interior_Icc] using hs))
    have bounds := anti (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [F] at bounds
    rw [segment.initial, segment.final] at bounds
    rw [inner_sub_right]
    change inner ℝ w (coordinateSpatialCLM q) - inner ℝ w (coordinateSpatialCLM p) ≤ _
    linarith
  let d := (coordinateSpatialSplit q).2 - (coordinateSpatialSplit p).2
  by_cases zero : d = 0
  · have time := functional 0 (by simp)
    change ‖d‖ ≤ q 0 - p 0
    simpa only [zero, norm_zero, inner_zero_left] using time
  · have positive : 0 < ‖d‖ := norm_pos_iff.mpr zero
    have normalized : ‖‖d‖⁻¹ • d‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos positive, inv_mul_cancel₀ (ne_of_gt positive)]
    have bound := functional (‖d‖⁻¹ • d) normalized
    change inner ℝ (‖d‖⁻¹ • d) d ≤ q 0 - p 0 at bound
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at bound
    have identity : ‖d‖⁻¹ * ‖d‖ ^ 2 = ‖d‖ := by field_simp
    rw [identity] at bound
    exact bound

def EHMetricFuture (nu : ℝ) (D : Set CoordinatePoint) (p q : CoordinatePoint) : Prop :=
  Relation.ReflTransGen (fun x y => Nonempty (EHFutureCausalSegment nu D x y)) p q

theorem metric_future_implies_flat {nu : ℝ} {D : Set CoordinatePoint} {p q : CoordinatePoint}
    (causal : EHMetricFuture nu D p q) : flatFutureOrder p q := by
  induction causal with
  | refl => exact flat_future_refl p
  | @tail q z before segment ih =>
    exact flat_future_trans ih segment.some.flat_order

def straightCausalSegment (nu : ℝ) (p q : CoordinatePoint)
    (hp : p ∈ protectedDiamond nu) (hq : q ∈ protectedDiamond nu) (order : flatFutureOrder p q) :
    EHFutureCausalSegment nu (protectedDiamond nu) p q where
  path := fun s => (1 - s) • p + s • q
  regular := by fun_prop
  initial := by simp
  final := by simp
  inside := by
    intro s hs
    exact protected_diamond_convex nu hp hq (sub_nonneg.mpr hs.2) hs.1 (by ring)
  future := by
    intro s hs
    have derivative : HasDerivAt (fun s : ℝ => (1 - s) • p + s • q) (q - p) s := by
      convert (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).smul_const p).add
        ((hasDerivAt_id s).smul_const q) using 1 <;> simp [sub_eq_add_neg, add_comm]
    rw [derivative.deriv, actual_future_tangent_iff]
    change ‖coordinateSpatialCLM (q - p)‖ ≤ q 0 - p 0
    rw [map_sub]
    exact order

theorem metric_future_iff_flat_on_diamond (nu : ℝ) (p q : CoordinatePoint)
    (hp : p ∈ protectedDiamond nu) (hq : q ∈ protectedDiamond nu) :
    EHMetricFuture nu (protectedDiamond nu) p q ↔ flatFutureOrder p q := by
  constructor
  · exact metric_future_implies_flat
  · intro order
    exact Relation.ReflTransGen.single ⟨straightCausalSegment nu p q hp hq order⟩

end AASCKleinGordon.CurvedKG
