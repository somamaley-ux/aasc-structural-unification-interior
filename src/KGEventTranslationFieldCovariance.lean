import KGEventTranslationFieldOperations
import KGSpacetimeEventTranslationTests
import KGAxisBoostTranslationCompatibility

noncomputable section
set_option maxHeartbeats 1400000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem spacetimeFieldCore_eventTranslation (a : Parameters) (b : Spacetime) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    coreEventTranslation a b (spacetimeFieldCore a s h u)=
      spacetimeFieldCore a s (spacetimeEventTranslationTestCLM b h) (coreEventTranslation a b u) := by
  simp only [spacetimeFieldCore,LinearMap.smul_apply,LinearMap.add_apply,map_smul,map_add,
    eventTranslation_creationCore,eventTranslation_annihilationCore,
    conjugate_spacetimeEventTranslationTest,spacetimeSmearing_eventTranslation]

theorem fockSpacetimeField_eventTranslation_on_original_core (a : Parameters) (b : Spacetime) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    fockEventTranslation a b (fockSpacetimeField a s h (includedFockCore a u))=
      fockSpacetimeField a s (spacetimeEventTranslationTestCLM b h)
        (includedFockCore a (coreEventTranslation a b u)) := by
  rw [fockSpacetimeField_on_original_core,fockEventTranslation_intertwines_original_core,
    spacetimeFieldCore_eventTranslation,fockSpacetimeField_on_original_core]

theorem coreEventTranslation_fixes_vacuum (a : Parameters) (b : Spacetime) :
    coreEventTranslation a b vacuumCore=vacuumCore := by
  apply finiteParticleCoreToFock_injective a
  rw [← fockEventTranslation_intertwines_original_core]
  exact fockEventTranslation_fixes_vacuum a b

def coreEventTranslationEquiv (a : Parameters) (b : Spacetime) :
    FiniteParticleCore ≃ₗ[ℂ] FiniteParticleCore where
  toLinearMap := coreEventTranslation a b
  invFun := coreEventTranslation a (-b)
  left_inv := coreEventTranslation_inverse a b
  right_inv u := by simpa only [neg_neg] using coreEventTranslation_inverse a (-b) u

theorem coreAxisBoost_eventTranslation (a : Parameters) (r : ℝ) (b : Spacetime)
    (u : FiniteParticleCore) :
    coreAxisBoost a r (coreEventTranslation a b u)=
      coreEventTranslation a (spacetimeAxisBoostCLE r b) (coreAxisBoost a r u) := by
  apply finiteParticleCoreToFock_injective a
  rw [← fockAxisBoost_intertwines_original_core,← fockEventTranslation_intertwines_original_core,
    fockAxisBoost_eventTranslation,fockAxisBoost_intertwines_original_core,
    fockEventTranslation_intertwines_original_core]

def coreAxisPoincare (a : Parameters) (b : Spacetime) (r : ℝ) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  (coreEventTranslation a b).comp (coreAxisBoost a r)

theorem fockAxisPoincare_intertwines_original_core (a : Parameters) (b : Spacetime) (r : ℝ)
    (u : FiniteParticleCore) :
    fockAxisPoincare a b r (finiteParticleCoreToFock a u)=
      finiteParticleCoreToFock a (coreAxisPoincare a b r u) := by
  change fockEventTranslation a b (fockAxisBoostUnitary a r (finiteParticleCoreToFock a u))=_
  rw [fockAxisBoost_intertwines_original_core,fockEventTranslation_intertwines_original_core]
  rfl

theorem coreAxisPoincare_mul (a : Parameters) (b d : Spacetime) (r t : ℝ) (u : FiniteParticleCore) :
    coreAxisPoincare a b r (coreAxisPoincare a d t u)=
      coreAxisPoincare a (b+spacetimeAxisBoostCLE r d) (r+t) u := by
  apply finiteParticleCoreToFock_injective a
  simp only [← fockAxisPoincare_intertwines_original_core,fockAxisPoincare_mul]

end AASCKleinGordon
