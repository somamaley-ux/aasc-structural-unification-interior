import KGSpacetimeSmearing
import SchwartzConjugation
import KGSchwartzSmearingLaws
import KGCoreTopologyRepresentation

/-! An actual spacetime-smeared field family on the ORIGINAL core, for one
fixed real amplitude s. Amplitude/action/EMT calibration is not assumed by
this construction. Real tests give the Segal combination; complex tests
are extended complex-linearly using conjugation on the annihilation smear. -/
noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

def spacetimeFieldCore (a : Parameters) (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  (s : ℂ) • (creationCore (spacetimeSmearingCLM a h) +
    annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)))

theorem spacetimeFieldCore_add_test (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ)) :
    spacetimeFieldCore a s (h+k) = spacetimeFieldCore a s h + spacetimeFieldCore a s k := by
  simp only [spacetimeFieldCore, map_add, conjugateSchwartz_add,
    creationCore_add_smear, annihilationCore_add_smear]
  module

theorem spacetimeFieldCore_smul_test (a : Parameters) (s : ℝ) (c : ℂ) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeFieldCore a s (c • h) = c • spacetimeFieldCore a s h := by
  simp only [spacetimeFieldCore, map_smul, conjugateSchwartz_smul,
    creationCore_smul_smear, annihilationCore_smul_smear, star_star]
  module

theorem spacetimeFieldCore_state_continuous (a : Parameters) (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    Continuous (spacetimeFieldCore a s h) :=
  ((creationCore_continuous _).add (annihilationCore_continuous a _)).const_smul (s : ℂ)

def fockSpacetimeField (a : Parameters) (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (spacetimeFieldCore a s h)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

theorem fockSpacetimeField_on_original_core (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (v : FiniteParticleCore) :
    fockSpacetimeField a s h (includedFockCore a v) =
      finiteParticleCoreToFock a (spacetimeFieldCore a s h v) := by
  change finiteParticleCoreToFock a (spacetimeFieldCore a s h
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a v))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fockSpacetimeField_preserves_original_core (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (v : fockCoreDomain a) :
    fockSpacetimeField a s h v ∈ fockCoreDomain a :=
  ⟨spacetimeFieldCore a s h ((fockCoreDomainEquiv a).symm v), rfl⟩

end AASCKleinGordon
