import KGSpacetimeFieldCore
import KGFockCoreAdjointness
import KGCreationSmearingContinuity
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
set_option maxHeartbeats 2400000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem annihilation_creation_original_core_inner (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (annihilationCore a f u)) (finiteParticleCoreToFock a v) =
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (creationCore f v)) := by
  have h := congrArg (starRingEnd ℂ) (creation_annihilation_original_core_inner a f v u)
  simpa only [inner_conj_symm] using h.symm

def positiveFieldFormCLM (a : Parameters) (u v : FiniteParticleCore) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (finiteParticleCoreToFock a u)).comp
    ((fockCreationSmearCLM a v).comp (spacetimeSmearingCLM a))

def negativeFieldFormCLM (a : Parameters) (u v : FiniteParticleCore) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ where
  toFun h := inner ℂ
    (fockCreationSmearCLM a u (spacetimeSmearingCLM a (conjugateSchwartzCLM h)))
    (finiteParticleCoreToFock a v)
  map_add' h k := by
    simp only [map_add, inner_add_left]
  map_smul' c h := by
    simp only [conjugateSchwartz_smul, map_smul, inner_smul_left]
    simp
  cont := (((fockCreationSmearCLM a u).continuous.comp
    ((spacetimeSmearingCLM a).continuous.comp conjugateSchwartzCLM.continuous)).inner continuous_const)

/-- Each actual matrix coefficient is a tempered distribution (a continuous
complex-linear functional on the spacetime Schwartz space). -/
def spacetimeFieldForm (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) :
    𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (s : ℂ) • (positiveFieldFormCLM a u v + negativeFieldFormCLM a u v)

theorem spacetimeFieldForm_eq_matrix_coefficient (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeFieldForm a s u v h =
      inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a (spacetimeFieldCore a s h v)) := by
  change (s : ℂ) * (inner ℂ (finiteParticleCoreToFock a u)
      (finiteParticleCoreToFock a (creationCore (spacetimeSmearingCLM a h) v)) +
    inner ℂ (finiteParticleCoreToFock a (creationCore
      (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) u)) (finiteParticleCoreToFock a v)) = _
  rw [creation_annihilation_original_core_inner a
    (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) u v]
  simp only [spacetimeFieldCore, LinearMap.smul_apply, LinearMap.add_apply,
    map_smul, map_add, inner_smul_right, inner_add_right]

theorem spacetimeFieldCore_adjoint_test (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (spacetimeFieldCore a s h u)) (finiteParticleCoreToFock a v) =
      inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a (spacetimeFieldCore a s (conjugateSchwartzCLM h) v)) := by
  simp only [spacetimeFieldCore, LinearMap.smul_apply, LinearMap.add_apply,
    conjugateSchwartz_involutive, map_smul, map_add, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right]
  rw [creation_annihilation_original_core_inner a (spacetimeSmearingCLM a h) u v,
    annihilation_creation_original_core_inner a
      (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) u v]
  simp only [Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => (s : ℂ) * z) (add_comm _ _)

theorem spacetimeFieldCore_real_test_symmetric (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (hh : conjugateSchwartzCLM h = h) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (spacetimeFieldCore a s h u)) (finiteParticleCoreToFock a v) =
      inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a (spacetimeFieldCore a s h v)) := by
  simpa only [hh] using spacetimeFieldCore_adjoint_test a s h u v

end AASCKleinGordon
