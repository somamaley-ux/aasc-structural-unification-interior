import KGPauliJordanNonvacuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
set_option maxHeartbeats 600000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem real_sin_temperate : Real.sin.HasTemperateGrowth := by
  refine ⟨Real.contDiff_sin,fun n => ⟨0,1,fun x => ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,pow_zero,mul_one] using
    Real.abs_iteratedDeriv_sin_le_one n x

theorem real_cos_temperate : Real.cos.HasTemperateGrowth := by
  refine ⟨Real.contDiff_cos,fun n => ⟨0,1,fun x => ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,Real.norm_eq_abs,pow_zero,mul_one] using
    Real.abs_iteratedDeriv_cos_le_one n x

def shellAngularFrequency (a : Parameters) (p : Momentum) : ℝ := energy a p/(a.speed*a.hbar)

theorem shellAngularFrequency_pos (a : Parameters) (p : Momentum) : 0<shellAngularFrequency a p :=
  div_pos (energy_pos a p) (mul_pos a.speed_pos a.hbar_pos)

theorem shellAngularFrequency_temperate (a : Parameters) : (shellAngularFrequency a).HasTemperateGrowth := by
  simpa only [shellAngularFrequency,div_eq_mul_inv] using
    (energy_temperate a).mul (Function.HasTemperateGrowth.const (a.speed*a.hbar)⁻¹)

theorem shellAngularFrequency_sq (a : Parameters) (p : Momentum) :
    shellAngularFrequency a p^2=momentumSq p/a.hbar^2+(massWaveNumber a)^2 := by
  dsimp [shellAngularFrequency,massWaveNumber]
  have hc : a.speed ≠ 0 := ne_of_gt a.speed_pos
  have hh : a.hbar ≠ 0 := ne_of_gt a.hbar_pos
  have he := energy_sq a p
  field_simp [hc,hh]
  nlinarith [he]

def temporalShellSine (a : Parameters) (t : ℝ) (p : Momentum) : ℝ := Real.sin (shellAngularFrequency a p*t)
def temporalShellCosine (a : Parameters) (t : ℝ) (p : Momentum) : ℝ := Real.cos (shellAngularFrequency a p*t)

theorem temporalShellSine_temperate (a : Parameters) (t : ℝ) : (temporalShellSine a t).HasTemperateGrowth :=
  real_sin_temperate.comp ((shellAngularFrequency_temperate a).mul (Function.HasTemperateGrowth.const t))
theorem temporalShellCosine_temperate (a : Parameters) (t : ℝ) : (temporalShellCosine a t).HasTemperateGrowth :=
  real_cos_temperate.comp ((shellAngularFrequency_temperate a).mul (Function.HasTemperateGrowth.const t))

def temporalShellSineCLM (a : Parameters) (t : ℝ) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p => (temporalShellSine a t p : ℂ))
def temporalShellCosineCLM (a : Parameters) (t : ℝ) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p => (temporalShellCosine a t p : ℂ))

theorem temporalShellSineCLM_apply (a : Parameters) (t : ℝ) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    temporalShellSineCLM a t f p=(temporalShellSine a t p : ℂ)*f p :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.hasTemperateGrowth.comp (temporalShellSine_temperate a t)) f p

theorem temporalShellCosineCLM_apply (a : Parameters) (t : ℝ) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    temporalShellCosineCLM a t f p=(temporalShellCosine a t p : ℂ)*f p :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.hasTemperateGrowth.comp (temporalShellCosine_temperate a t)) f p

theorem temporalShellSine_hasDerivAt (a : Parameters) (p : Momentum) (t : ℝ) :
    HasDerivAt (fun s => temporalShellSine a s p)
      (shellAngularFrequency a p*temporalShellCosine a t p) t := by
  convert ((hasDerivAt_id t).const_mul (shellAngularFrequency a p)).sin using 1 <;>
    simp [temporalShellSine,temporalShellCosine,mul_comm]

theorem temporalShellCosine_hasDerivAt (a : Parameters) (p : Momentum) (t : ℝ) :
    HasDerivAt (fun s => temporalShellCosine a s p)
      (-shellAngularFrequency a p*temporalShellSine a t p) t := by
  convert ((hasDerivAt_id t).const_mul (shellAngularFrequency a p)).cos using 1 <;>
    simp [temporalShellSine,temporalShellCosine,mul_comm]

end AASCKleinGordon
