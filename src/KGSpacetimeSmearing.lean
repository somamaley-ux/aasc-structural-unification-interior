import KGEnergyTemperate
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Actual Schwartz Fourier restriction to the SAME positive massive shell.
Spacetime coordinate x₀ is ct; the Euclidean Fourier covector is
(-E/c,p)/(2π hbar), so the standard Fourier kernel has phase
exp(i Et/hbar - i p·x/hbar). This fixes the test-map convention; field
amplitude and its action/EMT calibration are separate explicit obligations. -/
noncomputable section
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

abbrev Spacetime := EuclideanSpace ℝ (Fin 4)

def fourCoordinateCons : (ℝ × Momentum) ≃L[ℝ] FourMomentum :=
  ({ toEquiv := Fin.consEquiv (fun _ : Fin 4 => ℝ)
     map_add' := by intro x y; ext i; cases i using Fin.cases <;> rfl
     map_smul' := by intro c x; ext i; cases i using Fin.cases <;> rfl } :
    (ℝ × Momentum) ≃ₗ[ℝ] FourMomentum).toContinuousLinearEquiv

def fourCoordinateJoin : (ℝ × Momentum) ≃L[ℝ] Spacetime :=
  fourCoordinateCons.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm

def timeInjection : ℝ →L[ℝ] Spacetime :=
  fourCoordinateJoin.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ ℝ Momentum)

def spatialInjection : Momentum →L[ℝ] Spacetime :=
  fourCoordinateJoin.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ Momentum)

def shellCovector (a : Parameters) (p : Momentum) : Spacetime :=
  timeInjection (-energy a p/a.speed) + spatialInjection p

theorem shellCovector_eq_join (a : Parameters) (p : Momentum) :
    shellCovector a p = fourCoordinateJoin (-energy a p/a.speed,p) := by
  change fourCoordinateJoin (-energy a p/a.speed,0) + fourCoordinateJoin (0,p) = _
  rw [← map_add]
  simp

theorem shellCovector_temperate (a : Parameters) : (shellCovector a).HasTemperateGrowth := by
  have he : (fun p => -energy a p/a.speed).HasTemperateGrowth := by
    convert (Function.HasTemperateGrowth.const (-a.speed⁻¹)).mul (energy_temperate a) using 1
    funext p
    simp only [Pi.mul_apply, div_eq_mul_inv]
    ring
  exact (timeInjection.hasTemperateGrowth.comp he).add spatialInjection.hasTemperateGrowth

def fourierWaveScale (a : Parameters) : ℝ := (2*Real.pi*a.hbar)⁻¹

theorem fourierWaveScale_pos (a : Parameters) : 0 < fourierWaveScale a := by
  dsimp [fourierWaveScale]
  exact inv_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) a.hbar_pos)

def shellFrequency (a : Parameters) (p : Momentum) : Spacetime :=
  fourierWaveScale a • shellCovector a p

theorem shellFrequency_temperate (a : Parameters) : (shellFrequency a).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const (fourierWaveScale a)).smul (shellCovector_temperate a)

def frequencyRecovery (a : Parameters) : Spacetime →L[ℝ] Momentum :=
  (fourierWaveScale a)⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ Momentum).comp
    fourCoordinateJoin.symm.toContinuousLinearMap)

theorem frequencyRecovery_shellFrequency (a : Parameters) (p : Momentum) :
    frequencyRecovery a (shellFrequency a p) = p := by
  simp only [frequencyRecovery, shellFrequency, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, shellCovector_eq_join, smul_smul]
  change (fourierWaveScale a * (fourierWaveScale a)⁻¹) •
    (fourCoordinateJoin.symm (fourCoordinateJoin (-energy a p/a.speed,p))).2 = p
  rw [mul_inv_cancel₀ (fourierWaveScale_pos a).ne', one_smul,
    ContinuousLinearEquiv.symm_apply_apply]

def shellRestrictionCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.compCLM ℂ (shellFrequency_temperate a) (by
    refine ⟨1, ‖frequencyRecovery a‖, ?_⟩
    intro p
    rw [pow_one]
    calc
      ‖p‖ = ‖frequencyRecovery a (shellFrequency a p)‖ :=
        congrArg norm (frequencyRecovery_shellFrequency a p).symm
      _ ≤ ‖frequencyRecovery a‖ * ‖shellFrequency a p‖ := (frequencyRecovery a).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _))

@[simp] theorem shellRestrictionCLM_apply (a : Parameters) (h : 𝓢(Spacetime,ℂ)) (p : Momentum) :
    shellRestrictionCLM a h p = h (shellFrequency a p) := rfl

def spacetimeSmearingCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  (shellRestrictionCLM a).comp (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))

@[simp] theorem spacetimeSmearingCLM_apply (a : Parameters) (h : 𝓢(Spacetime,ℂ)) (p : Momentum) :
    spacetimeSmearingCLM a h p = (𝓕 h) (shellFrequency a p) := rfl

end AASCKleinGordon
