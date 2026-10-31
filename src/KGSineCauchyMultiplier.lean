import KGTemporalShellCoefficients

noncomputable section
set_option maxHeartbeats 600000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem inverseShellFrequency_bessel (a : Parameters) (p : Momentum) :
    (shellAngularFrequency a p)⁻¹ =
      (a.hbar/(a.mass*a.speed))*(1+‖scaledMomentumCLM a p‖^2)^(-(1/(2:ℝ))) := by
  rw [Real.rpow_neg (by positivity : 0 ≤ 1+‖scaledMomentumCLM a p‖^2),← Real.sqrt_eq_rpow,
    shellAngularFrequency,energy_bessel]
  have hm : a.mass ≠ 0 := ne_of_gt a.mass_pos
  have hc : a.speed ≠ 0 := ne_of_gt a.speed_pos
  have hh : a.hbar ≠ 0 := ne_of_gt a.hbar_pos
  have hs : Real.sqrt (1+‖scaledMomentumCLM a p‖^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp
  <;> ring

theorem inverseShellFrequency_temperate (a : Parameters) :
    (fun p => (shellAngularFrequency a p)⁻¹).HasTemperateGrowth := by
  have he : (fun p => (shellAngularFrequency a p)⁻¹) =
      (fun p => (a.hbar/(a.mass*a.speed))*(1+‖scaledMomentumCLM a p‖^2)^(-(1/(2:ℝ)))) :=
    funext (inverseShellFrequency_bessel a)
  rw [he]
  exact (Function.HasTemperateGrowth.const _).mul
    ((Function.hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin 3))
      (-(1/(2:ℝ)))).comp (scaledMomentumCLM a).hasTemperateGrowth)

/-- Multiplier of the homogeneous sine solution with zero position and unit velocity. -/
def sineCauchyCoefficient (a : Parameters) (t : ℝ) (p : Momentum) : ℝ :=
  temporalShellSine a t p*(shellAngularFrequency a p)⁻¹

theorem sineCauchyCoefficient_temperate (a : Parameters) (t : ℝ) :
    (sineCauchyCoefficient a t).HasTemperateGrowth :=
  (temporalShellSine_temperate a t).mul (inverseShellFrequency_temperate a)

def sineCauchyMultiplier (a : Parameters) (t : ℝ) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p => (sineCauchyCoefficient a t p : ℂ))

theorem sineCauchyMultiplier_apply (a : Parameters) (t : ℝ) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    sineCauchyMultiplier a t f p = (sineCauchyCoefficient a t p : ℂ)*f p :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.hasTemperateGrowth.comp (sineCauchyCoefficient_temperate a t)) f p

theorem sineCauchyCoefficient_zero (a : Parameters) (p : Momentum) :
    sineCauchyCoefficient a 0 p = 0 := by
  simp [sineCauchyCoefficient,temporalShellSine]

theorem temporalShellCosine_zero (a : Parameters) (p : Momentum) :
    temporalShellCosine a 0 p = 1 := by simp [temporalShellCosine]

theorem sineCauchyCoefficient_hasDerivAt (a : Parameters) (t : ℝ) (p : Momentum) :
    HasDerivAt (fun s => sineCauchyCoefficient a s p) (temporalShellCosine a t p) t := by
  have hn : shellAngularFrequency a p ≠ 0 := ne_of_gt (shellAngularFrequency_pos a p)
  convert (temporalShellSine_hasDerivAt a p t).mul_const (shellAngularFrequency a p)⁻¹ using 1
  · field_simp [hn]

theorem sineCauchyCoefficient_initial_velocity (a : Parameters) (p : Momentum) :
    HasDerivAt (fun s => sineCauchyCoefficient a s p) 1 0 := by
  simpa only [temporalShellCosine_zero] using sineCauchyCoefficient_hasDerivAt a 0 p

theorem sineCauchyCoefficient_acceleration (a : Parameters) (t : ℝ) (p : Momentum) :
    HasDerivAt (fun s => temporalShellCosine a s p)
      (-(momentumSq p/a.hbar^2+(massWaveNumber a)^2)*sineCauchyCoefficient a t p) t := by
  have hn : shellAngularFrequency a p ≠ 0 := ne_of_gt (shellAngularFrequency_pos a p)
  convert temporalShellCosine_hasDerivAt a p t using 1
  rw [← shellAngularFrequency_sq]
  unfold sineCauchyCoefficient
  field_simp
  <;> ring

end AASCKleinGordon
