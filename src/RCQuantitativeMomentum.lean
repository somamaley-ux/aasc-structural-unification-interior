import RCMomentumCutoff

/-! The finite-momentum SR free comparison on the actual retained multiplier flows. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

def cutoffError (a : Parameters) (c t P : ℝ) : ℝ :=
  |t| * P^4/(8*a.hbar*a.mass^3*c^2)

theorem cutoff_error_nonnegative (a : Parameters) (c t P : ℝ) : 0 ≤ cutoffError a c t P := by
  have hm := a.mass_pos
  have hh := a.hbar_pos
  unfold cutoffError
  positivity

theorem phase_cutoff_bound (a : Parameters) (c : ℝ) (hc : 0 < c) (t P : ℝ)
    (p : Momentum) (inside : momentumSq p ≤ P^2) :
    ‖Translation.phase a.hbar t (kgNRDispersion a c p) -
      Translation.phase a.hbar t (kgNRKineticEnergy a p)‖ ≤ min 2 (cutoffError a c t P) := by
  apply le_min (phase_difference_two a c t p)
  apply (phase_difference_bound a c hc t p).trans
  have power : momentumSq p^2 ≤ P^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr inside) (add_nonneg (sq_nonneg P) (momentumSq_nonneg p))]
  have hh := a.hbar_pos
  have hm := a.mass_pos
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left power (abs_nonneg t)) (by positivity)

theorem momentum_flow_difference_ae (a : Parameters) (c t : ℝ) (f : KGNRMomentumHilbert) :
    kgNRMomentumFlow a c t f - kgNRFreeMomentumFlow a t f =ᵐ[volume]
      (fun p => (Translation.phase a.hbar t (kgNRDispersion a c p)-
        Translation.phase a.hbar t (kgNRKineticEnergy a p))*f p) := by
  filter_upwards [Lp.coeFn_sub (kgNRMomentumFlow a c t f) (kgNRFreeMomentumFlow a t f),
    Multiplication.phaseMultiplier_ae (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t f,
    Multiplication.phaseMultiplier_ae (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a) a.hbar t f]
      with p hp hc hn
  simp only [Pi.sub_apply] at hp
  rw [hp]
  change Multiplication.phaseMultiplier (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t f p-
    Multiplication.phaseMultiplier (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a) a.hbar t f p = _
  rw [hc,hn,sub_mul]

theorem momentum_cutoff_evolution_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert) :
    ‖kgNRMomentumFlow a c t (momentumCutoff P f)-kgNRFreeMomentumFlow a t (momentumCutoff P f)‖ ≤
      min 2 (cutoffError a c t P)*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [momentum_flow_difference_ae a c t (momentumCutoff P f),momentum_cutoff_ae P f] with p hp hq
  rw [hp,hq]
  by_cases inside : momentumSq p ≤ P^2
  · simp only [cutoffSymbol,if_pos inside,one_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right (phase_cutoff_bound a c hc t P p inside) (norm_nonneg _)
  · simp only [cutoffSymbol,if_neg inside,zero_mul,mul_zero,norm_zero]
    exact mul_nonneg (le_min (by norm_num) (cutoff_error_nonnegative a c t P)) (norm_nonneg _)

def cutoffEvolutionDifference (a : Parameters) (c t P : ℝ) :
    KGNRMomentumHilbert →L[ℂ] KGNRMomentumHilbert :=
  ((kgNRMomentumFlow a c t).toContinuousLinearEquiv.toContinuousLinearMap -
    (kgNRFreeMomentumFlow a t).toContinuousLinearEquiv.toContinuousLinearMap).comp (momentumCutoff P)

theorem cutoff_evolution_operator_bound (a : Parameters) (c : ℝ) (hc : 0 < c) (t P : ℝ) :
    ‖cutoffEvolutionDifference a c t P‖ ≤ min 2 (cutoffError a c t P) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_min (by norm_num) (cutoff_error_nonnegative a c t P))
  exact momentum_cutoff_evolution_bound a c hc t P

theorem momentum_evolution_tail_bound (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert) :
    ‖kgNRMomentumFlow a c t f-kgNRFreeMomentumFlow a t f‖ ≤
      cutoffError a c t P*‖f‖+2*‖f-momentumCutoff P f‖ := by
  let q := momentumCutoff P f
  have split : kgNRMomentumFlow a c t f-kgNRFreeMomentumFlow a t f =
      (kgNRMomentumFlow a c t q-kgNRFreeMomentumFlow a t q)+
        (kgNRMomentumFlow a c t (f-q)-kgNRFreeMomentumFlow a t (f-q)) := by
    simp only [map_sub]
    abel
  rw [split]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (momentum_cutoff_evolution_bound a c hc t P f).trans
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg f))
  · calc
      ‖kgNRMomentumFlow a c t (f-q)-kgNRFreeMomentumFlow a t (f-q)‖ ≤
          ‖kgNRMomentumFlow a c t (f-q)‖+‖kgNRFreeMomentumFlow a t (f-q)‖ := norm_sub_le _ _
      _ = 2*‖f-q‖ := by simp only [LinearIsometryEquiv.norm_map];ring

end AASCKleinGordon.RecoveryComparison
