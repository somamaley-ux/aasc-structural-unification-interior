import KGLorentzBoostSchwartz
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
namespace AASCKleinGordon

def momentumDotCLM (p : Momentum) : Momentum →L[ℝ] ℝ :=
  p 0 • ContinuousLinearMap.proj 0 + p 1 • ContinuousLinearMap.proj 1 +
    p 2 • ContinuousLinearMap.proj 2

def energyDerivativeCLM (a : Parameters) (p : Momentum) : Momentum →L[ℝ] ℝ :=
  (a.speed^2/energy a p) • momentumDotCLM p

theorem energy_hasFDerivAt (a : Parameters) (p : Momentum) :
    HasFDerivAt (energy a) (energyDerivativeCLM a p) p := by
  have hi (i : Fin 3) : HasFDerivAt (fun q : Momentum => q i) (ContinuousLinearMap.proj i) p :=
    (ContinuousLinearMap.proj i : Momentum →L[ℝ] ℝ).hasFDerivAt
  have hr := ((((hi 0).pow 2).add ((hi 1).pow 2)).add ((hi 2).pow 2)).const_mul (a.speed^2)
  have hs := (hr.const_add (a.mass^2*a.speed^4)).sqrt (energy_radicand_pos a p).ne'
  convert hs using 1
  ext v
  simp only [energyDerivativeCLM, momentumDotCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat, pow_one, Pi.add_apply]
  change (a.speed^2/energy a p)*(p 0*v 0+p 1*v 1+p 2*v 2) =
    (1/(2*energy a p))*(a.speed^2*(2*p 0*v 0+2*p 1*v 1+2*p 2*v 2))
  field_simp [(energy_pos a p).ne']

def axisBoostDerivativeCLM (a : Parameters) (r : ℝ) (p : Momentum) : Momentum →L[ℝ] Momentum :=
  ContinuousLinearMap.pi ![(Real.sinh r/a.speed) • energyDerivativeCLM a p +
    Real.cosh r • ContinuousLinearMap.proj 0,
    ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]

theorem axisBoostMomentum_hasFDerivAt (a : Parameters) (r : ℝ) (p : Momentum) :
    HasFDerivAt (axisBoostMomentum a r) (axisBoostDerivativeCLM a r p) p := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert ((energy_hasFDerivAt a p).const_mul (Real.sinh r/a.speed)).add
      ((ContinuousLinearMap.proj (0 : Fin 3) : Momentum →L[ℝ] ℝ).hasFDerivAt.const_mul (Real.cosh r)) using 1
    · funext q
      change Real.sinh r*(energy a q/a.speed) + Real.cosh r*q 0 =
        Real.sinh r/a.speed*energy a q + Real.cosh r*q 0
      ring
  · exact (ContinuousLinearMap.proj (1 : Fin 3) : Momentum →L[ℝ] ℝ).hasFDerivAt
  · exact (ContinuousLinearMap.proj (2 : Fin 3) : Momentum →L[ℝ] ℝ).hasFDerivAt

def axisBoostJacobian (a : Parameters) (r : ℝ) (p : Momentum) : ℝ :=
  Real.cosh r + Real.sinh r*a.speed*p 0/energy a p

theorem axisBoostDerivative_det (a : Parameters) (r : ℝ) (p : Momentum) :
    (axisBoostDerivativeCLM a r p).det = axisBoostJacobian a r p := by
  change LinearMap.det (axisBoostDerivativeCLM a r p).toLinearMap = _
  rw [← LinearMap.det_toMatrix']
  have hmat : LinearMap.toMatrix' (axisBoostDerivativeCLM a r p).toLinearMap =
      !![Real.cosh r + Real.sinh r/a.speed*(a.speed^2/energy a p)*p 0,
          Real.sinh r/a.speed*(a.speed^2/energy a p)*p 1,
          Real.sinh r/a.speed*(a.speed^2/energy a p)*p 2;
        0,1,0; 0,0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [axisBoostDerivativeCLM, energyDerivativeCLM, momentumDotCLM, LinearMap.toMatrix'_apply] <;> ring
  rw [hmat, Matrix.det_fin_three]
  norm_num
  dsimp [axisBoostJacobian]
  field_simp [a.speed_pos.ne', (energy_pos a p).ne']
  ring

theorem axisBoostJacobian_eq_energy_ratio (a : Parameters) (r : ℝ) (p : Momentum) :
    axisBoostJacobian a r p = energy a (axisBoostMomentum a r p)/energy a p := by
  have he := axisBoostMomentum_energy a r p
  dsimp [axisBoostTime] at he
  dsimp [axisBoostJacobian]
  have hc := a.speed_pos.ne'
  have hp := (energy_pos a p).ne'
  field_simp [hc, hp] at he ⊢
  nlinarith [he]

theorem axisBoostJacobian_pos (a : Parameters) (r : ℝ) (p : Momentum) :
    0 < axisBoostJacobian a r p := by
  rw [axisBoostJacobian_eq_energy_ratio]
  exact div_pos (energy_pos a _) (energy_pos a _)

theorem axisBoost_wigner_weight_jacobian (a : Parameters) (r : ℝ) (p : Momentum) :
    wignerWeight a (axisBoostMomentum a r p) * axisBoostJacobian a r p = wignerWeight a p := by
  rw [axisBoostJacobian_eq_energy_ratio]
  dsimp [wignerWeight]
  field_simp [(energy_pos a (axisBoostMomentum a r p)).ne', (energy_pos a p).ne']

end AASCKleinGordon
