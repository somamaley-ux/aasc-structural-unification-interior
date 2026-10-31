import KGSchwartzMassShellEquation
import KGSpacetimeFieldForms
import KGSpacetimeFieldCCR

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem creationCore_zero_smear : creationCore (0 : 𝓢(Momentum,ℂ)) = 0 := by
  simpa only [zero_smul] using creationCore_smul_smear (0 : ℂ) (0 : 𝓢(Momentum,ℂ))

theorem annihilationCore_zero_smear (a : Parameters) :
    annihilationCore a (0 : 𝓢(Momentum,ℂ)) = 0 := by
  simpa only [zero_smul, star_zero] using
    annihilationCore_smul_smear a (0 : ℂ) (0 : 𝓢(Momentum,ℂ))

theorem spacetimeFieldCore_kleinGordon (a : Parameters) (s : ℝ) (h : 𝓢(Spacetime,ℂ)) :
    spacetimeFieldCore a s (kleinGordonSchwartzCLM a h) = 0 := by
  rw [spacetimeFieldCore, spacetimeSmearing_kleinGordon_zero,
    spacetimeSmearing_conjugate_kleinGordon_zero, creationCore_zero_smear,
    annihilationCore_zero_smear, zero_add, smul_zero]

theorem fockSpacetimeField_kleinGordon_on_original_domain (a : Parameters) (s : ℝ)
    (h : 𝓢(Spacetime,ℂ)) (v : fockCoreDomain a) :
    fockSpacetimeField a s (kleinGordonSchwartzCLM a h) v = 0 := by
  change finiteParticleCoreToFock a
    (spacetimeFieldCore a s (kleinGordonSchwartzCLM a h)
      ((fockCoreDomainEquiv a).symm v)) = 0
  rw [spacetimeFieldCore_kleinGordon a s h, LinearMap.zero_apply, map_zero]

theorem spacetimeFieldForm_kleinGordon (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) :
    (spacetimeFieldForm a s u v).comp (kleinGordonSchwartzCLM a) = 0 := by
  ext h
  change spacetimeFieldForm a s u v (kleinGordonSchwartzCLM a h) = 0
  rw [spacetimeFieldForm_eq_matrix_coefficient a s u v (kleinGordonSchwartzCLM a h),
    spacetimeFieldCore_kleinGordon a s h,
    LinearMap.zero_apply, map_zero, inner_zero_right]

end AASCKleinGordon
