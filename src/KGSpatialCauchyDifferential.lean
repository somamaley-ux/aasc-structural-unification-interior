import KGSpectralCauchyFamilies
import KGLocalizedEnergyIntegration

noncomputable section
set_option maxHeartbeats 1200000
open scoped SchwartzMap FourierTransform
open LineDeriv
namespace AASCKleinGordon

def kgSpatialPartialCLM (i : Fin 3) : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  lineDerivOpCLM ℂ 𝓢(KGSpatialSpace,ℂ) (kgSpatialDirection i)

theorem kgSpatialPartial_apply (i : Fin 3) (f : 𝓢(KGSpatialSpace,ℂ)) (x : KGSpatialSpace) :
    kgSpatialPartialCLM i f x=fderiv ℝ f x (kgSpatialDirection i) := rfl

theorem spatialFourier_injective {f g : 𝓢(KGSpatialSpace,ℂ)}
    (h : (𝓕 f : 𝓢(KGSpatialSpace,ℂ))=𝓕 g) : f=g := by
  have hh := congrArg (fun q : 𝓢(KGSpatialSpace,ℂ) => (𝓕⁻ q : 𝓢(KGSpatialSpace,ℂ))) h
  simpa only [FourierTransform.fourierInv_fourier_eq] using hh

theorem fourier_kgSpatialPartial (i : Fin 3) (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (kgSpatialPartialCLM i f) ξ=((2*Real.pi*ξ i : ℝ) : ℂ)*Complex.I*𝓕 f ξ := by
  change (𝓕 (∂_{kgSpatialDirection i} f)) ξ=_
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : KGSpatialSpace => inner ℝ x (kgSpatialDirection i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (kgSpatialDirection i)).hasTemperateGrowth
  change (2*Real.pi*Complex.I) •
    (SchwartzMap.smulLeftCLM ℂ (fun x : KGSpatialSpace => inner ℝ x (kgSpatialDirection i)) (𝓕 f) ξ)=_
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [kgSpatialDirection,EuclideanSpace.inner_single_right,one_mul,conj_trivial,
    RCLike.real_smul_eq_coe_mul,smul_eq_mul]
  change (2*(Real.pi : ℂ)*Complex.I)*((ξ i : ℂ)*𝓕 f ξ)=_
  push_cast
  ring

theorem fourier_spatialSineSolution (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (spatialSineSolutionCLM a t f) ξ=(spatialSineCoefficient a t ξ : ℂ)*𝓕 f ξ := by
  rw [spatialSineSolution_apply,FourierTransform.fourier_fourierInv_eq,spatialSineMultiplier_apply]

theorem fourier_spatialCosineSolution (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (spatialCosineSolutionCLM a t f) ξ=(spatialCosineCoefficient a t ξ : ℂ)*𝓕 f ξ := by
  rw [spatialCosineSolution_apply,FourierTransform.fourier_fourierInv_eq,spatialCosineMultiplier_apply]

theorem kgSpatialPartial_spatialSineSolution (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) (i : Fin 3) :
    kgSpatialPartialCLM i (spatialSineSolutionCLM a t f)=spatialSineSolutionCLM a t (kgSpatialPartialCLM i f) := by
  apply spatialFourier_injective
  ext ξ
  rw [fourier_kgSpatialPartial,fourier_spatialSineSolution,fourier_spatialSineSolution,fourier_kgSpatialPartial]
  ring

theorem kgSpatialPartial_spatialCosineSolution (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) (i : Fin 3) :
    kgSpatialPartialCLM i (spatialCosineSolutionCLM a t f)=spatialCosineSolutionCLM a t (kgSpatialPartialCLM i f) := by
  apply spatialFourier_injective
  ext ξ
  rw [fourier_kgSpatialPartial,fourier_spatialCosineSolution,fourier_spatialCosineSolution,fourier_kgSpatialPartial]
  ring

def kgSpatialLaplacian (f : 𝓢(KGSpatialSpace,ℂ)) : 𝓢(KGSpatialSpace,ℂ) :=
  ∑ i : Fin 3, kgSpatialPartialCLM i (kgSpatialPartialCLM i f)

def kgSpatialOperator (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) : 𝓢(KGSpatialSpace,ℂ) :=
  -kgSpatialLaplacian f+((massWaveNumber a)^2 : ℂ) • f

theorem fourier_kgSpatialLaplacian (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (kgSpatialLaplacian f) ξ=-(((2*Real.pi)^2*‖ξ‖^2 : ℝ) : ℂ)*𝓕 f ξ := by
  have hi (i : Fin 3) : 𝓕 (kgSpatialPartialCLM i (kgSpatialPartialCLM i f)) ξ=
      -((2*Real.pi*ξ i : ℝ) : ℂ)^2*𝓕 f ξ := by
    rw [fourier_kgSpatialPartial,fourier_kgSpatialPartial]
    calc
      _ = Complex.I^2*(((2*Real.pi*ξ i : ℝ) : ℂ)^2*𝓕 f ξ) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  simp only [kgSpatialLaplacian,FourierTransform.fourier_sum,SchwartzMap.sum_apply,hi]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton,Real.norm_eq_abs,sq_abs]
  push_cast
  ring

theorem fourier_kgSpatialOperator (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 (kgSpatialOperator a f) ξ=((spatialOmega a ξ)^2 : ℂ)*𝓕 f ξ := by
  simp only [kgSpatialOperator,FourierTransform.fourier_add,FourierTransform.fourier_neg,
    FourierTransform.fourier_smul,SchwartzMap.add_apply,SchwartzMap.neg_apply,
    SchwartzMap.smul_apply,fourier_kgSpatialLaplacian,smul_eq_mul]
  have hs := spatialSpectralFrequency_sq a ξ
  change spatialOmega a ξ^2=_ at hs
  have hsC : (spatialOmega a ξ : ℂ)^2=
      (((2*Real.pi)^2*‖ξ‖^2+(massWaveNumber a)^2 : ℝ) : ℂ) := by exact_mod_cast hs
  rw [hsC]
  push_cast
  ring

theorem spatialAcceleration_eq_neg_sine_operator (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialAccelerationSolutionCLM a t f= -spatialSineSolutionCLM a t (kgSpatialOperator a f) := by
  apply spatialFourier_injective
  ext ξ
  rw [spatialAccelerationSolution_apply,FourierTransform.fourier_fourierInv_eq,
    spatialAccelerationMultiplier_apply]
  simp only [FourierTransform.fourier_neg,SchwartzMap.neg_apply,fourier_spatialSineSolution,fourier_kgSpatialOperator,
    spatialSineCoefficient,sineCauchyCoefficient]
  have hn : (spatialOmega a ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (spatialOmega_pos a ξ))
  change ((-spatialOmega a ξ*temporalShellSine a t (spatialSpectralMomentumCLM a ξ) : ℝ) : ℂ)*𝓕 f ξ=
    -(((temporalShellSine a t (spatialSpectralMomentumCLM a ξ)* (spatialOmega a ξ)⁻¹ : ℝ) : ℂ)*
      (((spatialOmega a ξ : ℂ)^2)*𝓕 f ξ))
  push_cast
  field_simp
  <;> ring

end AASCKleinGordon
