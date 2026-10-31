import KGAxisBoostStrongContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter LineDeriv
open scoped SchwartzMap Topology
namespace AASCKleinGordon

def particleFirstDirection (n : ℕ) (i : Fin n) : ParticleConfiguration n :=
  Pi.single i (Pi.single 0 (1 : ℝ))

def particleAxisBoostVector (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    ParticleConfiguration n := fun i => Pi.single 0 (-(energy a (x i)/a.speed))

theorem particleAxisBoostVector_sum (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleAxisBoostVector a n x =
      ∑ i : Fin n, (-(energy a (x i)/a.speed)) • particleFirstDirection n i := by
  classical
  ext i j
  simp only [particleAxisBoostVector,particleFirstDirection,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,Pi.single_apply]
  by_cases hj : j=0 <;> simp [hj,ite_apply,Pi.single_apply]

theorem axisBoostMomentum_inverse_hasDerivAt (a : Parameters) (r : ℝ) (p : Momentum) :
    HasDerivAt (fun s => axisBoostMomentum a (-s) p)
      (Pi.single 0 (-(energy a (axisBoostMomentum a (-r) p)/a.speed))) r := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun s => Real.sinh (-s)*(energy a p/a.speed)+Real.cosh (-s)*p 0)
      (-(energy a (axisBoostMomentum a (-r) p)/a.speed)) r
    have h := (((Real.hasDerivAt_sinh (-r)).comp r (hasDerivAt_neg r)).mul_const
      (energy a p/a.speed)).add
      (((Real.hasDerivAt_cosh (-r)).comp r (hasDerivAt_neg r)).mul_const (p 0))
    convert h using 1
    rw [axisBoostMomentum_energy]
    dsimp [axisBoostTime]
    ring
  · change HasDerivAt (fun _ : ℝ => p 1) 0 r
    exact hasDerivAt_const r _
  · change HasDerivAt (fun _ : ℝ => p 2) 0 r
    exact hasDerivAt_const r _

theorem particleAxisBoost_inverse_hasDerivAt (a : Parameters) (n : ℕ) (r : ℝ)
    (x : ParticleConfiguration n) :
    HasDerivAt (fun s => particleAxisBoostME a n (-s) x)
      (particleAxisBoostVector a n (particleAxisBoostME a n (-r) x)) r := by
  apply hasDerivAt_pi.mpr
  intro i
  exact axisBoostMomentum_inverse_hasDerivAt a r (x i)

theorem particleBoostCoefficientReal_temperate (a : Parameters) (n : ℕ) (i : Fin n) :
    (fun x : ParticleConfiguration n => -(energy a (x i)/a.speed)).HasTemperateGrowth := by
  have h := ((energy_temperate a).comp
    (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum).hasTemperateGrowth).mul
    (Function.HasTemperateGrowth.const (-a.speed⁻¹))
  convert h using 1
  funext x
  change -(energy a (x i)/a.speed) = energy a (x i)*(-a.speed⁻¹)
  simp only [div_eq_mul_inv,mul_neg]

theorem particleBoostCoefficient_temperate (a : Parameters) (n : ℕ) (i : Fin n) :
    (fun x : ParticleConfiguration n => ((-(energy a (x i)/a.speed) : ℝ) : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (particleBoostCoefficientReal_temperate a n i)

def particleAxisBoostDifferential (a : Parameters) (n : ℕ) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  ∑ i : Fin n, (SchwartzMap.smulLeftCLM ℂ
    (fun x : ParticleConfiguration n => ((-(energy a (x i)/a.speed) : ℝ) : ℂ))).comp
      (lineDerivOpCLM ℂ 𝓢(ParticleConfiguration n,ℂ) (particleFirstDirection n i))

theorem particleAxisBoostDifferential_apply (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    particleAxisBoostDifferential a n H x = fderiv ℝ H x (particleAxisBoostVector a n x) := by
  classical
  simp only [particleAxisBoostDifferential,ContinuousLinearMap.sum_apply,SchwartzMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  simp_rw [SchwartzMap.smulLeftCLM_apply_apply (particleBoostCoefficient_temperate a n _)]
  rw [particleAxisBoostVector_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change ((-(energy a (x i)/a.speed) : ℝ) : ℂ) •
    (fderiv ℝ H x (particleFirstDirection n i)) = _
  simp only [smul_eq_mul,RCLike.real_smul_eq_coe_mul]
  rfl

theorem particleAxisBoost_schwartz_pointwise_hasDerivAt (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) (r : ℝ) :
    HasDerivAt (fun s => H (particleAxisBoostME a n (-s) x))
      (particleAxisBoostDifferential a n H (particleAxisBoostME a n (-r) x)) r := by
  rw [particleAxisBoostDifferential_apply]
  exact H.differentiableAt.hasFDerivAt.comp_hasDerivAt r
    (particleAxisBoost_inverse_hasDerivAt a n r x)

end AASCKleinGordon
