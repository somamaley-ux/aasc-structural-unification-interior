import WickOneParticleSpectral
import WickCovariantElasticSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

def wickCovariantTestRescale (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  (wickCovariantRoot a : ℂ)⁻¹ • ContinuousLinearMap.id ℂ _

theorem wick_covariant_test_rescale_apply (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantTestRescale a f=(wickCovariantRoot a : ℂ)⁻¹ • f := rfl

theorem wick_covariant_test_rescale_inverse (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantSchwartz a (wickCovariantTestRescale a f)=f := by
  have hr : (wickCovariantRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  change (wickCovariantRoot a : ℂ) • ((wickCovariantRoot a : ℂ)⁻¹ • f)=f
  rw [smul_smul,mul_inv_cancel₀ hr,one_smul]

theorem wick_covariant_test_rescale_surjective (a : Parameters) :
    Function.Surjective (wickCovariantTestRescale a) := by
  intro f
  refine ⟨wickCovariantSchwartz a f,?_⟩
  have hr : (wickCovariantRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  change (wickCovariantRoot a : ℂ)⁻¹ • ((wickCovariantRoot a : ℂ) • f)=f
  rw [smul_smul,inv_mul_cancel₀ hr,one_smul]

def wickCovariantNaturalTest (a : Parameters) :
    𝓢(Momentum,ℂ) →L[ℂ] WickCovariantHilbert a :=
  (wickCovariantNormalization a).toLinearIsometry.toContinuousLinearMap.comp
    ((oneParticleSchwartzToHilbert a).comp (wickCovariantTestRescale a))

theorem wick_covariant_natural_test_ae (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantNaturalTest a f=ᵐ[wickCovariantMeasure a] f := by
  exact (wick_covariant_normalization_schwartz_ae a (wickCovariantTestRescale a f)).trans
    (ae_of_all _ fun p => congrArg (fun g : 𝓢(Momentum,ℂ) => g p)
      (wick_covariant_test_rescale_inverse a f))

theorem wick_covariant_natural_test_injective (a : Parameters) :
    Function.Injective (wickCovariantNaturalTest a) := by
  intro f g h
  have he := oneParticleSchwartz_injective a ((wickCovariantNormalization a).injective h)
  exact (wick_covariant_test_rescale_inverse a f).symm.trans
    ((congrArg (wickCovariantSchwartz a) he).trans (wick_covariant_test_rescale_inverse a g))

theorem wick_covariant_natural_test_dense (a : Parameters) :
    DenseRange (wickCovariantNaturalTest a) := by
  have h₁ := (oneParticleSchwartz_dense a).comp
    (wick_covariant_test_rescale_surjective a).denseRange (oneParticleSchwartzToHilbert a).continuous
  exact (wickCovariantNormalization a).surjective.denseRange.comp h₁
    (wickCovariantNormalization a).continuous

def wickSectorOneOfSchwartzCLM : 𝓢(Momentum,ℂ) →L[ℂ] bosonicSchwartz 1 :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ oneConfigurationEquiv).codRestrict
    (bosonicSchwartz 1) (fun f => (sectorOneOfSchwartz f).property)

theorem wick_sector_one_roundtrip (f : 𝓢(Momentum,ℂ)) :
    sectorOneToSchwartz (wickSectorOneOfSchwartzCLM f)=f := by
  ext p
  change f (oneConfigurationEquiv (oneConfigurationEquiv.symm p))=f p
  rw [ContinuousLinearEquiv.apply_symm_apply]

def wickCovariantOriginalSector (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] bosonicSchwartz 1 :=
  wickSectorOneOfSchwartzCLM.comp (wickCovariantTestRescale a)

theorem wick_covariant_original_sector_coordinates (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    sectorOneToSchwartz (wickCovariantOriginalSector a f)=wickCovariantTestRescale a f :=
  wick_sector_one_roundtrip _

theorem wick_covariant_original_sector_wavefunction (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantSchwartz a (sectorOneToSchwartz (wickCovariantOriginalSector a f))=f := by
  rw [wick_covariant_original_sector_coordinates,wick_covariant_test_rescale_inverse]

theorem wick_covariant_original_sector_surjective (a : Parameters) :
    Function.Surjective (wickCovariantOriginalSector a) := by
  intro f
  refine ⟨wickCovariantSchwartz a (sectorOneToSchwartz f),?_⟩
  apply sectorOneToSchwartz_injective
  rw [wick_covariant_original_sector_coordinates]
  have hr : (wickCovariantRoot a : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (wick_covariant_root_positive a).ne'
  change (wickCovariantRoot a : ℂ)⁻¹ •
    ((wickCovariantRoot a : ℂ) • sectorOneToSchwartz f)=sectorOneToSchwartz f
  rw [smul_smul,inv_mul_cancel₀ hr,one_smul]

def wickOneCoreCLM : bosonicSchwartz 1 →L[ℂ] FiniteParticleCore :=
  { toLinearMap := DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1
    cont := finiteParticleCore_lof_continuous 1 }

def wickCovariantOriginalCore (a : Parameters) : 𝓢(Momentum,ℂ) →L[ℂ] FiniteParticleCore :=
  wickOneCoreCLM.comp (wickCovariantOriginalSector a)

theorem wick_covariant_natural_original_core_square (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickIsolatedCovariantHilbert a (wickOriginalIsolatedCore a (wickCovariantOriginalSector a f))=
      wickCovariantNaturalTest a f := by
  rw [wick_isolated_covariant_original_core]
  change wickCovariantNormalization a
    (oneParticleSchwartzToHilbert a (sectorOneToSchwartz (wickCovariantOriginalSector a f)))=_
  rw [wick_covariant_original_sector_coordinates]
  rfl

end AASCKleinGordon
