import KGFockMaximalMultiplication
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Distribution.TemperateGrowth

noncomputable section
namespace AASCKleinGordon

def momentumEuclidean : Momentum ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm

theorem momentumEuclidean_norm_sq (p : Momentum) :
    ‖momentumEuclidean p‖^2=momentumSq p := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [momentumEuclidean,Fin.sum_univ_succ,momentumSq,Real.norm_eq_abs,sq_abs]
  ring

def scaledMomentumCLM (a : Parameters) : Momentum →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (1/(a.mass*a.speed)) • momentumEuclidean.toContinuousLinearMap

theorem scaledMomentum_norm_sq (a : Parameters) (p : Momentum) :
    ‖scaledMomentumCLM a p‖^2=(1/(a.mass*a.speed))^2*momentumSq p := by
  change ‖(1/(a.mass*a.speed)) • momentumEuclidean p‖^2=_
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,momentumEuclidean_norm_sq]

theorem energy_bessel (a : Parameters) (p : Momentum) :
    energy a p=a.mass*a.speed^2*Real.sqrt (1+‖scaledMomentumCLM a p‖^2) := by
  have hm : a.mass≠0 := ne_of_gt a.mass_pos
  have hc : a.speed≠0 := ne_of_gt a.speed_pos
  have hs := Real.sq_sqrt (by positivity : 0≤1+‖scaledMomentumCLM a p‖^2)
  have he : (a.mass*a.speed^2*Real.sqrt (1+‖scaledMomentumCLM a p‖^2))^2=
      energy a p^2 := by
    rw [mul_pow,hs,scaledMomentum_norm_sq,energy_sq]
    field_simp
  have hpos : 0≤a.mass*a.speed^2*Real.sqrt (1+‖scaledMomentumCLM a p‖^2) := by
    have := a.mass_pos
    positivity
  nlinarith [energy_pos a p]

theorem energy_temperate (a : Parameters) : (energy a).HasTemperateGrowth := by
  have he : energy a=(fun p => a.mass*a.speed^2*
      (1+‖scaledMomentumCLM a p‖^2)^(1/(2:ℝ))) := by
    funext p
    rw [energy_bessel,Real.sqrt_eq_rpow]
  rw [he]
  apply Function.HasTemperateGrowth.mul (by fun_prop)
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow (EuclideanSpace ℝ (Fin 3))
    (1/(2:ℝ))).comp (scaledMomentumCLM a).hasTemperateGrowth

theorem particleTotalEnergy_temperate (a : Parameters) (n : ℕ) :
    (particleTotalEnergy a n).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.sum
  intro i _
  exact (energy_temperate a).comp
    (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum).hasTemperateGrowth

end AASCKleinGordon
