import KGInverseFourierFamilies

noncomputable section
set_option maxHeartbeats 1000000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def spatialOmega (a : Parameters) (ξ : KGSpatialSpace) : ℝ :=
  shellAngularFrequency a (spatialSpectralMomentumCLM a ξ)

theorem spatialOmega_pos (a : Parameters) (ξ : KGSpatialSpace) : 0 < spatialOmega a ξ :=
  shellAngularFrequency_pos a _

theorem spatialOmega_temperate (a : Parameters) : (spatialOmega a).HasTemperateGrowth :=
  (shellAngularFrequency_temperate a).comp (spatialSpectralMomentumCLM a).hasTemperateGrowth

theorem spatialInverseOmega_temperate (a : Parameters) :
    (fun ξ => (spatialOmega a ξ)⁻¹).HasTemperateGrowth :=
  (inverseShellFrequency_temperate a).comp (spatialSpectralMomentumCLM a).hasTemperateGrowth

def spatialOmegaMultiplierCLM (a : Parameters) : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ => (spatialOmega a ξ : ℂ))

def spatialInverseOmegaMultiplierCLM (a : Parameters) : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ => (((spatialOmega a ξ)⁻¹ : ℝ) : ℂ))

theorem spatialOmegaMultiplier_apply (a : Parameters) (g : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    spatialOmegaMultiplierCLM a g ξ=(spatialOmega a ξ : ℂ)*g ξ :=
  SchwartzMap.smulLeftCLM_apply_apply (Complex.ofRealCLM.hasTemperateGrowth.comp (spatialOmega_temperate a)) g ξ

theorem spatialInverseOmegaMultiplier_apply (a : Parameters) (g : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    spatialInverseOmegaMultiplierCLM a g ξ=(((spatialOmega a ξ)⁻¹ : ℝ) : ℂ)*g ξ :=
  SchwartzMap.smulLeftCLM_apply_apply (Complex.ofRealCLM.hasTemperateGrowth.comp (spatialInverseOmega_temperate a)) g ξ

def spatialCosineCoefficient (a : Parameters) (t : ℝ) (ξ : KGSpatialSpace) : ℝ :=
  temporalShellCosine a t (spatialSpectralMomentumCLM a ξ)

theorem spatialCosineCoefficient_temperate (a : Parameters) (t : ℝ) :
    (spatialCosineCoefficient a t).HasTemperateGrowth :=
  (temporalShellCosine_temperate a t).comp (spatialSpectralMomentumCLM a).hasTemperateGrowth

def spatialCosineMultiplierCLM (a : Parameters) (t : ℝ) : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ => (spatialCosineCoefficient a t ξ : ℂ))

theorem spatialCosineMultiplier_apply (a : Parameters) (t : ℝ) (g : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    spatialCosineMultiplierCLM a t g ξ=(spatialCosineCoefficient a t ξ : ℂ)*g ξ :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.hasTemperateGrowth.comp (spatialCosineCoefficient_temperate a t)) g ξ

def spatialCosineSolutionCLM (a : Parameters) (t : ℝ) : 𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢(KGSpatialSpace,ℂ)).comp
    ((spatialCosineMultiplierCLM a t).comp (FourierTransform.fourierCLM ℂ 𝓢(KGSpatialSpace,ℂ)))

theorem spatialCosineSolution_apply (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialCosineSolutionCLM a t f=𝓕⁻ (spatialCosineMultiplierCLM a t (𝓕 f)) := rfl

def spatialAccelerationMultiplierCLM (a : Parameters) (t : ℝ) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ =>
    ((-spatialOmega a ξ*temporalShellSine a t (spatialSpectralMomentumCLM a ξ) : ℝ) : ℂ))

theorem spatialAccelerationMultiplier_apply (a : Parameters) (t : ℝ)
    (g : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    spatialAccelerationMultiplierCLM a t g ξ=
      ((-spatialOmega a ξ*temporalShellSine a t (spatialSpectralMomentumCLM a ξ) : ℝ) : ℂ)*g ξ := by
  apply SchwartzMap.smulLeftCLM_apply_apply
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    ((spatialOmega_temperate a).neg.mul
      ((temporalShellSine_temperate a t).comp (spatialSpectralMomentumCLM a).hasTemperateGrowth))

def spatialAccelerationSolutionCLM (a : Parameters) (t : ℝ) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢(KGSpatialSpace,ℂ)).comp
    ((spatialAccelerationMultiplierCLM a t).comp (FourierTransform.fourierCLM ℂ 𝓢(KGSpatialSpace,ℂ)))

theorem spatialAccelerationSolution_apply (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialAccelerationSolutionCLM a t f=𝓕⁻ (spatialAccelerationMultiplierCLM a t (𝓕 f)) := rfl

theorem spatialCosineSolution_zero (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialCosineSolutionCLM a 0 f=f := by
  rw [spatialCosineSolution_apply]
  have hz : spatialCosineMultiplierCLM a 0 (𝓕 f)=𝓕 f := by
    ext ξ
    rw [spatialCosineMultiplier_apply]
    simp [spatialCosineCoefficient,temporalShellCosine_zero]
  rw [hz,FourierTransform.fourierInv_fourier_eq]

end AASCKleinGordon
