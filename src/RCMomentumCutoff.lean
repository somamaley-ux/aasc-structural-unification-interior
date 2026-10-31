import RCDispersionError

/-! An auxiliary spectral projection on the full physical momentum L2 carrier.
It is not asserted to preserve the original licensed smooth preparation core. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

def cutoffSymbol (P : ℝ) (p : Momentum) : ℂ := if momentumSq p ≤ P^2 then 1 else 0

theorem cutoff_symbol_measurable (P : ℝ) : Measurable (cutoffSymbol P) := by
  apply Measurable.ite ?_ measurable_const measurable_const
  have h : Continuous (fun p : Momentum => momentumSq p) := by unfold momentumSq;fun_prop
  exact measurableSet_le h.measurable measurable_const

theorem cutoff_symbol_bound (P : ℝ) (p : Momentum) : ‖cutoffSymbol P p‖ ≤ 1 := by
  unfold cutoffSymbol
  split_ifs <;> norm_num

def momentumCutoff (P : ℝ) : KGNRMomentumHilbert →L[ℂ] KGNRMomentumHilbert :=
  Multiplication.boundedMul (cutoffSymbol P) (cutoff_symbol_measurable P).aestronglyMeasurable
    1 (Eventually.of_forall (cutoff_symbol_bound P))

theorem momentum_cutoff_ae (P : ℝ) (f : KGNRMomentumHilbert) :
    momentumCutoff P f =ᵐ[volume] (fun p => cutoffSymbol P p * f p) :=
  Multiplication.boundedMul_ae _ _ _ _ f

theorem momentum_cutoff_contraction (P : ℝ) (f : KGNRMomentumHilbert) :
    ‖momentumCutoff P f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [momentum_cutoff_ae P f] with p hp
  rw [hp,norm_mul]
  exact (mul_le_mul_of_nonneg_right (cutoff_symbol_bound P p) (norm_nonneg _)).trans_eq (one_mul _)

theorem momentum_cutoff_idempotent (P : ℝ) (f : KGNRMomentumHilbert) :
    momentumCutoff P (momentumCutoff P f) = momentumCutoff P f := by
  apply Lp.ext
  filter_upwards [momentum_cutoff_ae P (momentumCutoff P f),momentum_cutoff_ae P f] with p hp hf
  rw [hp,hf]
  unfold cutoffSymbol
  split_ifs <;> simp

theorem cutoff_symbol_eventually_one (p : Momentum) :
    ∀ᶠ P : ℝ in atTop, cutoffSymbol P p = 1 := by
  filter_upwards [eventually_ge_atTop (max (momentumSq p) 1)] with P hP
  have h1 : 1 ≤ P := (le_max_right _ _).trans hP
  have hq : momentumSq p ≤ P := (le_max_left _ _).trans hP
  have inside : momentumSq p ≤ P^2 := by nlinarith
  exact if_pos inside

theorem momentum_cutoff_strong_exhaustion (f : KGNRMomentumHilbert) :
    Tendsto (fun P : ℝ => momentumCutoff P f) atTop (𝓝 f) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine Multiplication.L2_tendsto_zero_of_dominated _
    (fun P p => (cutoffSymbol P p-1)*f p) ?_ ?_
    (fun p => 2*‖f p‖) ((Lp.memLp f).norm.const_mul 2) ?_ ?_
  · intro P
    filter_upwards [Lp.coeFn_sub (momentumCutoff P f) f,momentum_cutoff_ae P f] with p hp hf
    simp only [Pi.sub_apply] at hp
    rw [hp,hf]
    ring
  · intro P
    exact (((cutoff_symbol_measurable P).aestronglyMeasurable.sub aestronglyMeasurable_const).mul
      (Lp.memLp f).1)
  · exact Eventually.of_forall (fun P => Eventually.of_forall (fun p => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by
        rw [norm_one]
        linarith [cutoff_symbol_bound P p])))
  · exact Eventually.of_forall (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_symbol_eventually_one p] with P hp
      simp [hp])

end AASCKleinGordon.RecoveryComparison
