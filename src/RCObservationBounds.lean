import RCFourierRecovery

/-! Typed continuous observations. No estimate here identifies discrete answers
or first failures at finite c; those require the retained exact source maps. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

section HilbertObservations
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem linear_observation_error (L : H →L[ℂ] ℂ) (u v : H) :
    ‖L u-L v‖ ≤ ‖L‖*‖u-v‖ := by
  rw [←map_sub]
  exact L.le_opNorm _

theorem overlap_error (z u v : H) :
    ‖inner ℂ z u-inner ℂ z v‖ ≤ ‖z‖*‖u-v‖ := by
  rw [←inner_sub_right]
  exact norm_inner_le_norm _ _

theorem unit_overlap_error (z u v : H) (hz : ‖z‖=1) :
    |‖inner ℂ z u‖-‖inner ℂ z v‖| ≤ ‖u-v‖ := by
  exact (abs_norm_sub_norm_le _ _).trans (by simpa only [hz,one_mul] using overlap_error z u v)

theorem unit_probability_error (z u v : H) (hz : ‖z‖=1) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    |‖inner ℂ z u‖^2-‖inner ℂ z v‖^2| ≤ 2*‖u-v‖ := by
  have aBound : ‖inner ℂ z u‖ ≤ 1 := by simpa only [hz,hu,mul_one] using norm_inner_le_norm z u
  have bBound : ‖inner ℂ z v‖ ≤ 1 := by simpa only [hz,hv,mul_one] using norm_inner_le_norm z v
  have identity : |‖inner ℂ z u‖^2-‖inner ℂ z v‖^2| =
      |‖inner ℂ z u‖-‖inner ℂ z v‖| * (‖inner ℂ z u‖+‖inner ℂ z v‖) := by
    rw [show ‖inner ℂ z u‖^2-‖inner ℂ z v‖^2 =
      (‖inner ℂ z u‖-‖inner ℂ z v‖)*(‖inner ℂ z u‖+‖inner ℂ z v‖) by ring,abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [identity]
  calc
    |‖inner ℂ z u‖-‖inner ℂ z v‖| * (‖inner ℂ z u‖+‖inner ℂ z v‖) ≤
        ‖u-v‖*(‖inner ℂ z u‖+‖inner ℂ z v‖) :=
      mul_le_mul_of_nonneg_right (unit_overlap_error z u v hz) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖u-v‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem normalized_probability_error (z u v : KGQuantum.PureVector H)
    (hz : ‖z.val‖=1) (hu : ‖u.val‖=1) (hv : ‖v.val‖=1) :
    |KGQuantum.transitionProbability z u-KGQuantum.transitionProbability z v| ≤ 2*‖u.val-v.val‖ := by
  simpa only [KGQuantum.transitionProbability,hz,hu,hv,one_pow,one_mul,div_one] using
    unit_probability_error z.val u.val v.val hz hu hv

end HilbertObservations

theorem momentum_linear_observation_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert) (L : KGNRMomentumHilbert →L[ℂ] ℂ) :
    ‖L (kgNRMomentumFlow a c t f)-L (kgNRFreeMomentumFlow a t f)‖ ≤
      ‖L‖*(cutoffError a c t P*‖f‖+2*‖f-momentumCutoff P f‖) :=
  (linear_observation_error L _ _).trans (mul_le_mul_of_nonneg_left
    (momentum_evolution_tail_bound a c hc t P f) (norm_nonneg L))

theorem momentum_probability_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f z : KGNRMomentumHilbert) (hf : ‖f‖=1) (hz : ‖z‖=1) :
    |‖inner ℂ z (kgNRMomentumFlow a c t f)‖^2-‖inner ℂ z (kgNRFreeMomentumFlow a t f)‖^2| ≤
      2*(cutoffError a c t P*‖f‖+2*‖f-momentumCutoff P f‖) :=
  (unit_probability_error z _ _ hz ((kgNRMomentumFlow a c t).norm_map f |>.trans hf)
    ((kgNRFreeMomentumFlow a t).norm_map f |>.trans hf)).trans
      (mul_le_mul_of_nonneg_left (momentum_evolution_tail_bound a c hc t P f) (by norm_num))

theorem spatial_linear_observation_compact_time (a : Parameters) (f : KGNRSpatialHilbert)
    (L : KGNRSpatialHilbert →L[ℂ] ℂ) (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖L (kgOriginalRestSpatialFlow a c t f)-L (kgNRSpatialFreeFlow a t f)‖ < epsilon := by
  have denominator : 0 < ‖L‖+1 := by positivity
  filter_upwards [spatial_compact_time_strong a f T hT (epsilon/(‖L‖+1)) (div_pos positive denominator)] with c hc
  intro t ht
  have bound := linear_observation_error L (kgOriginalRestSpatialFlow a c t f) (kgNRSpatialFreeFlow a t f)
  have state := hc t ht
  have scaled := mul_lt_mul_of_pos_left state denominator
  rw [mul_div_cancel₀ _ denominator.ne'] at scaled
  nlinarith [norm_nonneg (kgOriginalRestSpatialFlow a c t f-kgNRSpatialFreeFlow a t f),norm_nonneg L]

theorem spatial_probability_compact_time (a : Parameters) (f z : KGNRSpatialHilbert)
    (hf : ‖f‖=1) (hz : ‖z‖=1) (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      |‖inner ℂ z (kgOriginalRestSpatialFlow a c t f)‖^2-
        ‖inner ℂ z (kgNRSpatialFreeFlow a t f)‖^2| < epsilon := by
  filter_upwards [spatial_compact_time_strong a f T hT (epsilon/2) (by linarith),
    eventually_gt_atTop (0:ℝ)] with c hc hpos
  intro t ht
  have normOriginal : ‖kgOriginalRestSpatialFlow a c t f‖=1 := by
    unfold kgOriginalRestSpatialFlow
    rw [kg_transported_isolated_rest_flow_eq a c hpos]
    simpa only [LinearIsometryEquiv.norm_map] using hf
  have normLimit : ‖kgNRSpatialFreeFlow a t f‖=1 := (kgNRSpatialFreeFlow a t).norm_map f |>.trans hf
  have estimate := unit_probability_error z _ _ hz normOriginal normLimit
  have state := hc t ht
  linarith

end AASCKleinGordon.RecoveryComparison
