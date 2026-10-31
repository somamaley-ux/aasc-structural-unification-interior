import KGGeneralLorentzCoreAttachment
import KGGeneralLorentzSpacetime
import KGEventTranslationFieldCovariance

noncomputable section
set_option maxHeartbeats 1200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem lorentz_annihilationCore (a : Parameters) (L : ProperLorentzTransform)
    (f : 𝓢(Momentum,ℂ)) (v : FiniteParticleCore) :
    coreLorentz a L (annihilationCore a f v)=
      annihilationCore a (lorentzSchwartzCLM a L f) (coreLorentz a L v) := by
  apply original_core_inner_ext a
  intro w
  let u:=coreLorentz a L⁻¹ w
  have hu : coreLorentz a L u=w := by
    dsimp only [u]
    rw [coreLorentz_mul,mul_inv_cancel,coreLorentz_one]
  calc
    inner ℂ (finiteParticleCoreToFock a w)
        (finiteParticleCoreToFock a (coreLorentz a L (annihilationCore a f v)))=
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (annihilationCore a f v)) := by
        rw [← hu,coreLorentz_preserves_inner]
    _=inner ℂ (finiteParticleCoreToFock a (creationCore f u)) (finiteParticleCoreToFock a v) :=
      (creation_annihilation_original_core_inner a f u v).symm
    _=inner ℂ (finiteParticleCoreToFock a (coreLorentz a L (creationCore f u)))
        (finiteParticleCoreToFock a (coreLorentz a L v)) := (coreLorentz_preserves_inner a L _ _).symm
    _=inner ℂ (finiteParticleCoreToFock a w)
        (finiteParticleCoreToFock a (annihilationCore a (lorentzSchwartzCLM a L f) (coreLorentz a L v))) := by
      rw [lorentz_creationCore,creation_annihilation_original_core_inner,hu]

theorem spacetimeLorentzTest_one (h : 𝓢(Spacetime,ℂ)) : spacetimeLorentzTestCLM 1 h=h := by
  ext x
  simp only [spacetimeLorentzTest_apply,inv_one,spacetimeLorentz_one]

theorem spacetimeLorentzTest_mul (L M : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeLorentzTestCLM L (spacetimeLorentzTestCLM M h)=spacetimeLorentzTestCLM (L*M) h := by
  ext x
  simp only [spacetimeLorentzTest_apply,mul_inv_rev,spacetimeLorentz_mul]

theorem conjugate_spacetimeLorentzTest (L : ProperLorentzTransform) (h : 𝓢(Spacetime,ℂ)) :
    conjugateSchwartzCLM (spacetimeLorentzTestCLM L h)=
      spacetimeLorentzTestCLM L (conjugateSchwartzCLM h) := by ext x; rfl

theorem spacetimeFieldCore_lorentz (a : Parameters) (L : ProperLorentzTransform) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    coreLorentz a L (spacetimeFieldCore a s h u)=
      spacetimeFieldCore a s (spacetimeLorentzTestCLM L h) (coreLorentz a L u) := by
  simp only [spacetimeFieldCore,LinearMap.smul_apply,LinearMap.add_apply,map_smul,map_add,
    lorentz_creationCore,lorentz_annihilationCore,conjugate_spacetimeLorentzTest,spacetimeSmearing_lorentz]

theorem fockSpacetimeField_lorentz_on_original_core (a : Parameters) (L : ProperLorentzTransform)
    (s : ℝ) (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    fockLorentzUnitary a L (fockSpacetimeField a s h (includedFockCore a u))=
      fockSpacetimeField a s (spacetimeLorentzTestCLM L h) (includedFockCore a (coreLorentz a L u)) := by
  rw [fockSpacetimeField_on_original_core,fockLorentz_intertwines_original_core,
    spacetimeFieldCore_lorentz,fockSpacetimeField_on_original_core]

end AASCKleinGordon
