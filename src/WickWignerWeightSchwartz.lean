import WickOriginalSpatialJacobian

noncomputable section
set_option maxHeartbeats 1500000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_wigner_weight_bessel (a : Parameters) (p : Momentum) :
    wignerWeight a p=(1+‖scaledMomentumCLM a p‖^2)^(-(1/(2:ℝ))) := by
  rw [wignerWeight,energy_bessel,Real.rpow_neg (by positivity),← Real.sqrt_eq_rpow]
  have mass : a.mass≠0 := a.mass_pos.ne'
  have speed : a.speed≠0 := a.speed_pos.ne'
  field_simp

theorem wick_wigner_weight_temperate (a : Parameters) : (wignerWeight a).HasTemperateGrowth := by
  have h := (Function.hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin 3))
    (-(1/(2:ℝ)))).comp (scaledMomentumCLM a).hasTemperateGrowth
  convert h using 1
  funext p
  exact wick_wigner_weight_bessel a p

theorem wick_wigner_weight_complex_temperate (a : Parameters) :
    (fun p => (wignerWeight a p : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (wick_wigner_weight_temperate a)

def wickWignerWeightSchwartzCLM (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun p => (wignerWeight a p : ℂ))

theorem wick_wigner_weight_schwartz_apply (a : Parameters) (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    wickWignerWeightSchwartzCLM a f p=(wignerWeight a p : ℂ)*f p :=
  SchwartzMap.smulLeftCLM_apply_apply (wick_wigner_weight_complex_temperate a) f p

end AASCKleinGordon
