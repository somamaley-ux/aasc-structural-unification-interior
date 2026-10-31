import KGSpacetimeAxisBoostMeasure
import KGAxisBoostFieldOperations
import KGSpacetimeFieldCore
import KGAxisBoostClosedDomain

noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

theorem spacetimeAxisBoostTest_zero (h : 𝓢(Spacetime,ℂ)) : spacetimeAxisBoostTestCLM 0 h=h := by
  ext x
  simp only [spacetimeAxisBoostTestCLM_apply,neg_zero,spacetimeAxisBoost_zero]

theorem spacetimeAxisBoostTest_add (r s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeAxisBoostTestCLM r (spacetimeAxisBoostTestCLM s h)=
      spacetimeAxisBoostTestCLM (r+s) h := by
  ext x
  change h (spacetimeAxisBoostCLE (-s) (spacetimeAxisBoostCLE (-r) x))=
    h (spacetimeAxisBoostCLE (-(r+s)) x)
  rw [← spacetimeAxisBoost_add]
  congr 2
  ring

theorem conjugate_spacetimeAxisBoostTest (r : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    conjugateSchwartzCLM (spacetimeAxisBoostTestCLM r h)=
      spacetimeAxisBoostTestCLM r (conjugateSchwartzCLM h) := by
  ext x
  rfl

theorem spacetimeSmearing_axisBoost (a : Parameters) (r : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeSmearingCLM a (spacetimeAxisBoostTestCLM r h)=
      axisBoostSchwartzCLM a r (spacetimeSmearingCLM a h) := by
  ext p
  change 𝓕 (spacetimeAxisBoostTestCLM r h) (shellFrequency a p)=
    𝓕 h (shellFrequency a (axisBoostMomentum a (-r) p))
  rw [fourier_spacetimeAxisBoostTest,shellFrequency_axisBoost]

theorem spacetimeFieldCore_axisBoost (a : Parameters) (r s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    coreAxisBoost a r (spacetimeFieldCore a s h u)=
      spacetimeFieldCore a s (spacetimeAxisBoostTestCLM r h) (coreAxisBoost a r u) := by
  simp only [spacetimeFieldCore,LinearMap.smul_apply,LinearMap.add_apply,
    map_smul,map_add,axisBoost_creationCore,axisBoost_annihilationCore,
    conjugate_spacetimeAxisBoostTest,spacetimeSmearing_axisBoost]

theorem fockSpacetimeField_axisBoost_on_original_core (a : Parameters) (r s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    fockAxisBoostUnitary a r (fockSpacetimeField a s h (includedFockCore a u))=
      fockSpacetimeField a s (spacetimeAxisBoostTestCLM r h)
        (includedFockCore a (coreAxisBoost a r u)) := by
  rw [fockSpacetimeField_on_original_core,fockAxisBoost_intertwines_original_core,
    spacetimeFieldCore_axisBoost,fockSpacetimeField_on_original_core]

end AASCKleinGordon
