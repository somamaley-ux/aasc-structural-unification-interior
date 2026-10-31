import KGSpacetimeEuclideanSplit
import KGPauliJordanNonvacuity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform ENNReal
namespace AASCKleinGordon

theorem energy_neg (a : Parameters) (p : Momentum) : energy a (-p)=energy a p := by
  simp [energy,momentumSq]

theorem wignerWeight_neg (a : Parameters) (p : Momentum) : wignerWeight a (-p)=wignerWeight a p := by
  simp only [wignerWeight,energy_neg]

theorem wignerWeight_inverse_shell_frequency (a : Parameters) (p : Momentum) :
    wignerWeight a p=(a.mass*a.speed/a.hbar)*(shellAngularFrequency a p)⁻¹ := by
  unfold wignerWeight shellAngularFrequency
  have hc := ne_of_gt a.speed_pos
  have hh := ne_of_gt a.hbar_pos
  have he := ne_of_gt (energy_pos a p)
  field_simp

theorem wigner_integral_eq_weighted_volume (a : Parameters) (g : Momentum → ℂ) :
    (∫ p, g p ∂wignerMeasure a)=∫ p, (wignerWeight a p : ℂ)*g p := by
  refine (integral_withDensity_eq_integral_toReal_smul (wignerDensity_measurable a)
    (Eventually.of_forall (fun p => by exact ENNReal.ofReal_lt_top)) g).trans ?_
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    change (ENNReal.ofReal (wignerWeight a p)).toReal • g p=(wignerWeight a p : ℂ)*g p
    rw [ENNReal.toReal_ofReal (wignerWeight_pos a p).le,RCLike.real_smul_eq_coe_mul]
    rfl

theorem wigner_weighted_schwartz_integrable (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    Integrable (fun p => (wignerWeight a p : ℂ)*g p) := by
  apply g.integrable.norm.mono'
    ((Complex.continuous_ofReal.comp (wignerWeight_continuous a)).mul g.continuous).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖(wignerWeight a p : ℂ)*g p‖ ≤ ‖g p‖
    simp only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (wignerWeight_pos a p)]
    exact mul_le_of_le_one_left (norm_nonneg _) (wignerWeight_le_one a p)

theorem wigner_integral_reflect (a : Parameters) (g : Momentum → ℂ) :
    (∫ p, g (-p) ∂wignerMeasure a)=∫ p, g p ∂wignerMeasure a := by
  rw [wigner_integral_eq_weighted_volume,wigner_integral_eq_weighted_volume]
  simpa only [wignerWeight_neg] using
    integral_neg_eq_self (fun p : Momentum => (wignerWeight a p : ℂ)*g p) volume

theorem massShellCommutator_eq_reflected_volume (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    massShellCommutatorCLM a h=
      (∫ p : Momentum, (wignerWeight a p : ℂ)*𝓕 h (shellFrequency a p))-
      (∫ p : Momentum, (wignerWeight a p : ℂ)*𝓕 h (-shellFrequency a (-p))) := by
  rw [massShellCommutator_apply]
  rw [← wigner_integral_reflect a (fun p => 𝓕 h (-shellFrequency a p))]
  rw [wigner_integral_eq_weighted_volume,wigner_integral_eq_weighted_volume]

theorem shellFrequency_spacetimeSpatialJoin (a : Parameters) (p : Momentum) :
    shellFrequency a p=spacetimeSpatialJoin
      (-shellAngularFrequency a p/(2*Real.pi),fourierWaveScale a • momentumEuclidean p) := by
  ext i
  cases i using Fin.cases with
  | zero =>
    rw [spacetimeSpatialJoin_zero]
    simp only [shellFrequency,shellCovector_eq_join,PiLp.smul_apply]
    change fourierWaveScale a*(-energy a p/a.speed) = -shellAngularFrequency a p/(2*Real.pi)
    unfold fourierWaveScale shellAngularFrequency
    field_simp
    <;> ring
  | succ i =>
    rw [spacetimeSpatialJoin_succ]
    simp only [shellFrequency,shellCovector_eq_join,PiLp.smul_apply]
    rfl

theorem reflectedNegativeShell_spacetimeSpatialJoin (a : Parameters) (p : Momentum) :
    -shellFrequency a (-p)=spacetimeSpatialJoin
      (shellAngularFrequency a p/(2*Real.pi),fourierWaveScale a • momentumEuclidean p) := by
  rw [shellFrequency_spacetimeSpatialJoin]
  have he : shellAngularFrequency a (-p)=shellAngularFrequency a p := by simp only [shellAngularFrequency,energy_neg]
  rw [he]
  ext i
  cases i using Fin.cases with
  | zero => simp only [PiLp.neg_apply,spacetimeSpatialJoin_zero,neg_div,neg_neg]
  | succ i =>
    simp only [PiLp.neg_apply,spacetimeSpatialJoin_succ,map_neg,PiLp.smul_apply,PiLp.neg_apply,
      smul_neg,neg_neg]

end AASCKleinGordon
