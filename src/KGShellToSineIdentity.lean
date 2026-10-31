import KGNormalizedShellTimeIntegrals

noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem positiveShell_weighted_volume_eq_time_integral (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    (∫ p : Momentum, (wignerWeight a p : ℂ)*𝓕 h (shellFrequency a p))=
      (2*Real.pi*a.hbar)^3 • ∫ ξ : KGSpatialSpace, ∫ t : ℝ,
        normalizedShellTimeIntegrand a h (-1) (t,ξ) := by
  rw [spatialSpectralMomentum_integral_change a]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    dsimp only
    rw [shellFrequency_spacetimeSpatialJoin,spatialSpectralMomentum_frequency_inverse,
      spacetimeFourier_eq_time_spatialFourier,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [normalizedShellTimeIntegrand,neg_one_mul,spatialOmega]
      ring

theorem reflectedNegativeShell_weighted_volume_eq_time_integral (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    (∫ p : Momentum, (wignerWeight a p : ℂ)*𝓕 h (-shellFrequency a (-p)))=
      (2*Real.pi*a.hbar)^3 • ∫ ξ : KGSpatialSpace, ∫ t : ℝ,
        normalizedShellTimeIntegrand a h 1 (t,ξ) := by
  rw [spatialSpectralMomentum_integral_change a]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    dsimp only
    rw [reflectedNegativeShell_spacetimeSpatialJoin,spatialSpectralMomentum_frequency_inverse,
      spacetimeFourier_eq_time_spatialFourier,← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      simp only [normalizedShellTimeIntegrand,one_mul,spatialOmega]
      ring

def shellSineNormalization (a : Parameters) : ℂ :=
  (2*Complex.I*((a.mass*a.speed/a.hbar : ℝ) : ℂ))*(((2*Real.pi*a.hbar)^3 : ℝ) : ℂ)

/-- Exact original shell distribution, with its original positive-minus-negative
shell sign, Wigner weight and Fourier convention. Tau is x0, not x0/c. -/
theorem massShellCommutator_eq_sine_time_integral (a : Parameters) (h : 𝓢(Spacetime,ℂ))
    (hc : HasCompactSupport (h : Spacetime → ℂ)) :
    massShellCommutatorCLM a h=shellSineNormalization a*
      ∫ t : ℝ, spatialSineSolutionCLM a t (spacetimeSpatialSliceCLM t h) 0 := by
  have hm := normalizedShellTimeIntegrand_integrable a h hc (-1)
  have hp := normalizedShellTimeIntegrand_integrable a h hc 1
  have hms : (∫ ξ : KGSpatialSpace, ∫ t : ℝ, normalizedShellTimeIntegrand a h (-1) (t,ξ))=
      ∫ t : ℝ, ∫ ξ : KGSpatialSpace, normalizedShellTimeIntegrand a h (-1) (t,ξ) :=
    (integral_integral_swap (f := fun t ξ => normalizedShellTimeIntegrand a h (-1) (t,ξ))
      (μ := volume) (ν := volume) hm).symm
  have hps : (∫ ξ : KGSpatialSpace, ∫ t : ℝ, normalizedShellTimeIntegrand a h 1 (t,ξ))=
      ∫ t : ℝ, ∫ ξ : KGSpatialSpace, normalizedShellTimeIntegrand a h 1 (t,ξ) :=
    (integral_integral_swap (f := fun t ξ => normalizedShellTimeIntegrand a h 1 (t,ξ))
      (μ := volume) (ν := volume) hp).symm
  rw [massShellCommutator_eq_reflected_volume,positiveShell_weighted_volume_eq_time_integral,
    reflectedNegativeShell_weighted_volume_eq_time_integral,hms,hps,← smul_sub,
    ← integral_integral_sub hm hp]
  have he : (∫ t : ℝ, ∫ ξ : KGSpatialSpace,
      normalizedShellTimeIntegrand a h (-1) (t,ξ)-normalizedShellTimeIntegrand a h 1 (t,ξ))=
      (2*Complex.I*((a.mass*a.speed/a.hbar : ℝ) : ℂ))*
        ∫ t : ℝ, spatialSineSolutionCLM a t (spacetimeSpatialSliceCLM t h) 0 := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [spatialSineSolution_at_origin,← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        dsimp only
        exact normalizedShellTimeIntegrand_difference a h t ξ
  rw [he]
  unfold shellSineNormalization
  rw [← smul_mul_assoc]
  congr 1
  change (((2*Real.pi*a.hbar)^3 : ℝ) : ℂ)*(2*Complex.I*((a.mass*a.speed/a.hbar : ℝ) : ℂ))=
    (2*Complex.I*((a.mass*a.speed/a.hbar : ℝ) : ℂ))*(((2*Real.pi*a.hbar)^3 : ℝ) : ℂ)
  exact mul_comm _ _

end AASCKleinGordon
