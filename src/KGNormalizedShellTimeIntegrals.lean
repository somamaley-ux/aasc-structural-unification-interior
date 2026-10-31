import KGSpacetimePartialFourierIdentity
import KGSpatialFourierFubiniMajorant
import KGWignerShellNormalization
import KGSpatialFourierVolume

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem spatialSpectralMomentum_frequency_inverse (a : Parameters) (ξ : KGSpatialSpace) :
    fourierWaveScale a • momentumEuclidean (spatialSpectralMomentumCLM a ξ)=ξ := by
  simp only [spatialSpectralMomentumCLM,ContinuousLinearMap.smul_apply,
    ContinuousLinearEquiv.coe_coe,map_smul,ContinuousLinearEquiv.apply_symm_apply,smul_smul]
  have he : fourierWaveScale a*(2*Real.pi*a.hbar)=1 := by
    unfold fourierWaveScale
    exact inv_mul_cancel₀ (by have := a.hbar_pos; positivity)
  rw [he,one_smul]

theorem temporalFourierKernel_shell_minus (ω t : ℝ) :
    temporalFourierKernel (-ω/(2*Real.pi)) t=Complex.exp (((ω*t : ℝ) : ℂ)*Complex.I) := by
  unfold temporalFourierKernel
  apply congrArg Complex.exp
  push_cast
  field_simp
  <;> ring

theorem temporalFourierKernel_shell_plus (ω t : ℝ) :
    temporalFourierKernel (ω/(2*Real.pi)) t=Complex.exp (((-(ω*t) : ℝ) : ℂ)*Complex.I) := by
  unfold temporalFourierKernel
  apply congrArg Complex.exp
  push_cast
  field_simp
  <;> ring

theorem temporalFourierKernel_shell_difference (ω t : ℝ) :
    temporalFourierKernel (-ω/(2*Real.pi)) t-temporalFourierKernel (ω/(2*Real.pi)) t=
      2*Complex.I*(Real.sin (ω*t) : ℂ) := by
  rw [temporalFourierKernel_shell_minus,temporalFourierKernel_shell_plus]
  simp only [Complex.exp_mul_I,Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg,
    ← Complex.ofReal_cos,← Complex.ofReal_sin]
  ring

def normalizedShellTimeIntegrand (a : Parameters) (h : 𝓢(Spacetime,ℂ)) (sign : ℝ)
    (z : ℝ × KGSpatialSpace) : ℂ :=
  (wignerWeight a (spatialSpectralMomentumCLM a z.2) : ℂ)*
    temporalFourierKernel (sign*spatialOmega a z.2/(2*Real.pi)) z.1*
    𝓕 (spacetimeSpatialSliceCLM z.1 h) z.2

theorem normalizedShellTimeIntegrand_integrable (a : Parameters) (h : 𝓢(Spacetime,ℂ))
    (hc : HasCompactSupport (h : Spacetime → ℂ)) (sign : ℝ) :
    Integrable (normalizedShellTimeIntegrand a h sign) := by
  have hi := compact_spatialSlice_fourier_integrable h hc
  have hw : Continuous (fun z : ℝ × KGSpatialSpace =>
      (wignerWeight a (spatialSpectralMomentumCLM a z.2) : ℂ)) :=
    Complex.continuous_ofReal.comp ((wignerWeight_continuous a).comp
      ((spatialSpectralMomentumCLM a).continuous.comp continuous_snd))
  have ho : Continuous (fun z : ℝ × KGSpatialSpace => spatialOmega a z.2) :=
    (spatialOmega_temperate a).1.continuous.comp continuous_snd
  have hp : Continuous (fun z : ℝ × KGSpatialSpace =>
      temporalFourierKernel (sign*spatialOmega a z.2/(2*Real.pi)) z.1) := by
    unfold temporalFourierKernel
    fun_prop
  apply hi.norm.mono' ((hw.mul hp).aestronglyMeasurable.mul hi.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖normalizedShellTimeIntegrand a h sign z‖ ≤ ‖𝓕 (spacetimeSpatialSliceCLM z.1 h) z.2‖
    simp only [normalizedShellTimeIntegrand,norm_mul,temporalFourierKernel_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (wignerWeight_pos a _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (wignerWeight_le_one a _)

theorem normalizedShellTimeIntegrand_difference (a : Parameters) (h : 𝓢(Spacetime,ℂ))
    (t : ℝ) (ξ : KGSpatialSpace) :
    normalizedShellTimeIntegrand a h (-1) (t,ξ)-normalizedShellTimeIntegrand a h 1 (t,ξ)=
      (2*Complex.I*((a.mass*a.speed/a.hbar : ℝ) : ℂ))*
        ((spatialSineCoefficient a t ξ : ℂ)*𝓕 (spacetimeSpatialSliceCLM t h) ξ) := by
  simp only [normalizedShellTimeIntegrand,neg_one_mul,one_mul]
  rw [← sub_mul,← mul_sub,temporalFourierKernel_shell_difference,
    wignerWeight_inverse_shell_frequency]
  unfold spatialSineCoefficient sineCauchyCoefficient temporalShellSine spatialOmega
  push_cast
  ring

end AASCKleinGordon
