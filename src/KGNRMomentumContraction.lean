import KGNRDispersion
import L2TranslationDerivative
import L2RealMultiplicationSelfAdjoint

/-! Strong scalar multiplier contraction on the fixed full momentum L² envelope.
The exact raw-symbol comparison is to the retained original KG energy.  An
isometric measure/sector identification with that original one-particle space,
spatial Fourier transport, and certified standing/composition remain separate
projection obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

theorem kg_nr_dispersion_measurable (a : Parameters) (c : ℝ) :
    Measurable (kgNRDispersion a c) := by
  unfold kgNRDispersion momentumSq
  fun_prop

theorem kg_nr_kinetic_measurable (a : Parameters) :
    Measurable (kgNRKineticEnergy a) := by
  unfold kgNRKineticEnergy momentumSq
  fun_prop

theorem kg_nr_phase_tendsto (a : Parameters) (t : ℝ) (p : Momentum) :
    Tendsto (fun c : ℝ => Translation.phase a.hbar t (kgNRDispersion a c p))
      atTop (nhds (Translation.phase a.hbar t (kgNRKineticEnergy a p))) := by
  have hc : Continuous (fun r : ℝ => Translation.phase a.hbar t r) := by
    unfold Translation.phase
    fun_prop
  exact hc.continuousAt.tendsto.comp (kg_nr_dispersion_tendsto a p)

/-- The finite-speed phase is exactly the rest-energy-subtracted original
mass-shell phase.  This assertion is confined to its scalar one-particle symbol. -/
theorem kg_nr_phase_original_symbol (a : Parameters) (c : ℝ) (hc : 0 < c)
    (t : ℝ) (p : Momentum) :
    Translation.phase a.hbar t (kgNRDispersion a c p) =
      Translation.phase a.hbar t (energy (kgNRParameters a c hc) p - a.mass * c ^ 2) := by
  rw [kg_nr_dispersion_is_rest_subtracted_energy]

abbrev KGNRMomentumHilbert := Lp ℂ 2 (volume : Measure Momentum)

def kgNRMomentumFlow (a : Parameters) (c t : ℝ) :
    KGNRMomentumHilbert ≃ₗᵢ[ℂ] KGNRMomentumHilbert :=
  Multiplication.phaseUnitary (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t

def kgNRFreeMomentumFlow (a : Parameters) (t : ℝ) :
    KGNRMomentumHilbert ≃ₗᵢ[ℂ] KGNRMomentumHilbert :=
  Multiplication.phaseUnitary (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a) a.hbar t

/-- Every vector in the full fixed momentum L² carrier has the controlled
rest-energy-subtracted scalar flow limit.  No compact-momentum assumption or
choice of representative is supplied. -/
theorem kg_nr_full_momentum_flow_strong_limit (a : Parameters) (t : ℝ)
    (f : KGNRMomentumHilbert) :
    Tendsto (fun c : ℝ => kgNRMomentumFlow a c t f) atTop
      (nhds (kgNRFreeMomentumFlow a t f)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine Multiplication.L2_tendsto_zero_of_dominated _
    (fun c p => (Translation.phase a.hbar t (kgNRDispersion a c p) -
      Translation.phase a.hbar t (kgNRKineticEnergy a p)) * f p)
    ?_ ?_ (fun p => 2 * ‖f p‖) ((Lp.memLp f).norm.const_mul 2) ?_ ?_
  · intro c
    filter_upwards [Lp.coeFn_sub (kgNRMomentumFlow a c t f) (kgNRFreeMomentumFlow a t f),
      Multiplication.phaseMultiplier_ae (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t f,
      Multiplication.phaseMultiplier_ae (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a) a.hbar t f]
      with p h1 h2 h3
    simp only [Pi.sub_apply] at h1
    change (kgNRMomentumFlow a c t f - kgNRFreeMomentumFlow a t f) p = _
    rw [h1]
    change Multiplication.phaseMultiplier (kgNRDispersion a c)
      (kg_nr_dispersion_measurable a c) a.hbar t f p -
      Multiplication.phaseMultiplier (kgNRKineticEnergy a)
        (kg_nr_kinetic_measurable a) a.hbar t f p = _
    rw [h2, h3, sub_mul]
  · intro c
    exact ((Multiplication.translationPhase_measurable _ (kg_nr_dispersion_measurable a c) a.hbar t).aestronglyMeasurable.sub
      (Multiplication.translationPhase_measurable _ (kg_nr_kinetic_measurable a) a.hbar t).aestronglyMeasurable).mul (Lp.memLp f).1
  · exact Eventually.of_forall (fun c => Eventually.of_forall (fun p => by
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc
        ‖Translation.phase a.hbar t (kgNRDispersion a c p) -
            Translation.phase a.hbar t (kgNRKineticEnergy a p)‖ ≤
          ‖Translation.phase a.hbar t (kgNRDispersion a c p)‖ +
            ‖Translation.phase a.hbar t (kgNRKineticEnergy a p)‖ := norm_sub_le _ _
        _ = 2 := by simp only [Translation.phase_norm]; norm_num))
  · exact Eventually.of_forall (fun p => by
      have h := ((kg_nr_phase_tendsto a t p).sub_const
        (Translation.phase a.hbar t (kgNRKineticEnergy a p))).mul_const (f p)
      simpa only [sub_self, zero_mul] using h)

theorem kg_nr_free_momentum_flow_continuous (a : Parameters) (f : KGNRMomentumHilbert) :
    Continuous (fun t => kgNRFreeMomentumFlow a t f) :=
  Multiplication.phaseMultiplier_strongly_continuous (kgNRKineticEnergy a)
    (kg_nr_kinetic_measurable a) a.hbar f

theorem kg_nr_free_momentum_flow_add (a : Parameters) (t s : ℝ) (f : KGNRMomentumHilbert) :
    kgNRFreeMomentumFlow a (t + s) f = kgNRFreeMomentumFlow a t (kgNRFreeMomentumFlow a s f) :=
  Multiplication.phaseMultiplier_add (kgNRKineticEnergy a) (kg_nr_kinetic_measurable a) a.hbar t s f

/-- The maximal quadratic-energy multiplier, with its actual maximal L²
domain rather than a supplied generator or kinetic certificate. -/
def kgNRFreeMomentumGenerator (a : Parameters) :
    KGNRMomentumHilbert →ₗ.[ℂ] KGNRMomentumHilbert :=
  Multiplication.realMultiplication (kgNRKineticEnergy a)

theorem kg_nr_free_momentum_generator_self_adjoint (a : Parameters) :
    IsSelfAdjoint (kgNRFreeMomentumGenerator a) :=
  Multiplication.realMultiplication_selfAdjoint (kgNRKineticEnergy a)
    (kg_nr_kinetic_measurable a)

theorem kg_nr_free_momentum_generator_dense (a : Parameters) :
    Dense ((kgNRFreeMomentumGenerator a).domain : Set KGNRMomentumHilbert) :=
  Multiplication.realMultiplication_dense_domain (kgNRKineticEnergy a)
    (kg_nr_kinetic_measurable a)

theorem kg_nr_free_momentum_flow_generator (a : Parameters)
    (f : (kgNRFreeMomentumGenerator a).domain) :
    HasDerivAt (fun t => kgNRFreeMomentumFlow a t f.val)
      (Translation.coefficient a.hbar • kgNRFreeMomentumGenerator a f) 0 :=
  Multiplication.phaseMultiplier_hasDerivAt_zero (kgNRKineticEnergy a)
    (kg_nr_kinetic_measurable a) a.hbar f

end AASCKleinGordon
