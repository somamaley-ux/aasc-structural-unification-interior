import KGSineCauchyMultiplier
import KGFlatEnergyAlgebra

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

/-- The exact change from Fourier cycles ξ to the original momentum p=2πℏ ξ. -/
def spatialSpectralMomentumCLM (a : Parameters) : KGSpatialSpace →L[ℝ] Momentum :=
  (2*Real.pi*a.hbar) • momentumEuclidean.symm.toContinuousLinearMap

theorem spatialSpectralMomentum_norm_sq (a : Parameters) (ξ : KGSpatialSpace) :
    momentumSq (spatialSpectralMomentumCLM a ξ)=(2*Real.pi*a.hbar)^2*‖ξ‖^2 := by
  rw [← momentumEuclidean_norm_sq]
  have he : momentumEuclidean (spatialSpectralMomentumCLM a ξ)=(2*Real.pi*a.hbar) • ξ := by
    simp [spatialSpectralMomentumCLM]
  rw [he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem spatialSpectralFrequency_sq (a : Parameters) (ξ : KGSpatialSpace) :
    shellAngularFrequency a (spatialSpectralMomentumCLM a ξ)^2=
      (2*Real.pi)^2*‖ξ‖^2+(massWaveNumber a)^2 := by
  rw [shellAngularFrequency_sq,spatialSpectralMomentum_norm_sq]
  have hh : a.hbar ≠ 0 := ne_of_gt a.hbar_pos
  field_simp
  <;> ring

def spatialSineCoefficient (a : Parameters) (t : ℝ) (ξ : KGSpatialSpace) : ℝ :=
  sineCauchyCoefficient a t (spatialSpectralMomentumCLM a ξ)

theorem spatialSineCoefficient_temperate (a : Parameters) (t : ℝ) :
    (spatialSineCoefficient a t).HasTemperateGrowth :=
  (sineCauchyCoefficient_temperate a t).comp (spatialSpectralMomentumCLM a).hasTemperateGrowth

def spatialSineMultiplierCLM (a : Parameters) (t : ℝ) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ => (spatialSineCoefficient a t ξ : ℂ))

theorem spatialSineMultiplier_apply (a : Parameters) (t : ℝ)
    (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    spatialSineMultiplierCLM a t f ξ=(spatialSineCoefficient a t ξ : ℂ)*f ξ :=
  SchwartzMap.smulLeftCLM_apply_apply
    (Complex.ofRealCLM.hasTemperateGrowth.comp (spatialSineCoefficient_temperate a t)) f ξ

/-- A genuine Schwartz-valued homogeneous sine family, built by Fourier conjugation. -/
def spatialSineSolutionCLM (a : Parameters) (t : ℝ) :
    𝓢(KGSpatialSpace,ℂ) →L[ℂ] 𝓢(KGSpatialSpace,ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢(KGSpatialSpace,ℂ)).comp
    ((spatialSineMultiplierCLM a t).comp (FourierTransform.fourierCLM ℂ 𝓢(KGSpatialSpace,ℂ)))

theorem spatialSineSolution_apply (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialSineSolutionCLM a t f=𝓕⁻ (spatialSineMultiplierCLM a t (𝓕 f)) := rfl

theorem spatialSineSolution_at_origin (a : Parameters) (t : ℝ) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialSineSolutionCLM a t f 0=∫ ξ, (spatialSineCoefficient a t ξ : ℂ)*𝓕 f ξ := by
  rw [spatialSineSolution_apply]
  rw [SchwartzMap.fourierInv_coe]
  rw [Real.fourierInv_eq]
  simp only [inner_zero_right,Real.fourierChar.map_zero_eq_one,one_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => spatialSineMultiplier_apply a t (𝓕 f) ξ)

theorem spatialSineSolution_zero (a : Parameters) (f : 𝓢(KGSpatialSpace,ℂ)) :
    spatialSineSolutionCLM a 0 f=0 := by
  rw [spatialSineSolution_apply]
  have hz : spatialSineMultiplierCLM a 0 (𝓕 f)=0 := by
    ext ξ
    rw [spatialSineMultiplier_apply]
    simp [spatialSineCoefficient,sineCauchyCoefficient_zero]
  rw [hz,FourierTransform.fourierInv_zero]

theorem spatialSineCoefficient_hasDerivAt (a : Parameters) (t : ℝ) (ξ : KGSpatialSpace) :
    HasDerivAt (fun s => spatialSineCoefficient a s ξ)
      (temporalShellCosine a t (spatialSpectralMomentumCLM a ξ)) t :=
  sineCauchyCoefficient_hasDerivAt a t (spatialSpectralMomentumCLM a ξ)

end AASCKleinGordon
