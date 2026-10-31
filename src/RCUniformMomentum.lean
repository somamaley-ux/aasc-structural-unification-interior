import RCQuantitativeMomentum

/-! Compact-time strong convergence, with explicit cutoff and tail control.
No unrestricted full-space operator norm limit is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter MeasureTheory
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

theorem cutoff_error_tendsto_zero (a : Parameters) (T P : ℝ) :
    Tendsto (fun c : ℝ => cutoffError a c T P) atTop (𝓝 0) := by
  have hinv : Tendsto (fun c : ℝ => (c⁻¹)^2) atTop (𝓝 (0:ℝ)) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 (0:ℝ))).pow 2
  have equal : (fun c : ℝ => cutoffError a c T P) =
      (fun c : ℝ => (|T| * P^4/(8*a.hbar*a.mass^3))*(c⁻¹)^2) := by
    funext c
    simp only [cutoffError,div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  rw [equal]
  simpa using hinv.const_mul (|T| * P^4/(8*a.hbar*a.mass^3))

theorem cutoff_error_time_bound (a : Parameters) (c t T P : ℝ)
    (hT : 0 ≤ T) (ht : |t| ≤ T) : cutoffError a c t P ≤ cutoffError a c T P := by
  have hh := a.hbar_pos
  have hm := a.mass_pos
  unfold cutoffError
  rw [abs_of_nonneg hT]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht (by positivity)) (by positivity)

theorem momentum_compact_time_strong (a : Parameters) (f : KGNRMomentumHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgNRMomentumFlow a c t f-kgNRFreeMomentumFlow a t f‖ < epsilon := by
  have tail : Tendsto (fun P : ℝ => ‖f-momentumCutoff P f‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => f) atTop (𝓝 f)).sub
      (momentum_cutoff_strong_exhaustion f)).norm
  have smallTail := (tendsto_order.mp tail).2 (epsilon/4) (by linarith)
  obtain ⟨P,hP⟩ := smallTail.exists
  have low : Tendsto (fun c : ℝ => cutoffError a c T P*‖f‖) atTop (𝓝 0) := by
    simpa using (cutoff_error_tendsto_zero a T P).mul_const ‖f‖
  filter_upwards [(tendsto_order.mp low).2 (epsilon/2) (by linarith),eventually_gt_atTop (0:ℝ)] with c hc hpos
  intro t ht
  have bound := momentum_evolution_tail_bound a c hpos t P f
  have timeBound := mul_le_mul_of_nonneg_right (cutoff_error_time_bound a c t T P hT ht) (norm_nonneg f)
  linarith

theorem original_covariant_compact_time_strong (a : Parameters) (f : KGNRMomentumHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgTransportedOriginalRestFlow a c t f-kgNRFreeMomentumFlow a t f‖ < epsilon := by
  filter_upwards [momentum_compact_time_strong a f T hT epsilon positive,eventually_gt_atTop (0:ℝ)] with c hc hp
  intro t ht
  rw [kg_transported_original_rest_flow_eq a c hp t f]
  exact hc t ht

theorem original_isolated_compact_time_strong (a : Parameters) (f : KGNRMomentumHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgTransportedIsolatedRestFlow a c t f-kgNRFreeMomentumFlow a t f‖ < epsilon := by
  filter_upwards [momentum_compact_time_strong a f T hT epsilon positive,eventually_gt_atTop (0:ℝ)] with c hc hp
  intro t ht
  rw [kg_transported_isolated_rest_flow_eq a c hp t f]
  exact hc t ht

theorem original_covariant_cutoff_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert) :
    ‖kgTransportedOriginalRestFlow a c t (momentumCutoff P f)-
      kgNRFreeMomentumFlow a t (momentumCutoff P f)‖ ≤ min 2 (cutoffError a c t P)*‖f‖ := by
  rw [kg_transported_original_rest_flow_eq a c hc]
  exact momentum_cutoff_evolution_bound a c hc t P f

theorem original_isolated_cutoff_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert) :
    ‖kgTransportedIsolatedRestFlow a c t (momentumCutoff P f)-
      kgNRFreeMomentumFlow a t (momentumCutoff P f)‖ ≤ min 2 (cutoffError a c t P)*‖f‖ := by
  rw [kg_transported_isolated_rest_flow_eq a c hc]
  exact momentum_cutoff_evolution_bound a c hc t P f

end AASCKleinGordon.RecoveryComparison
