import KGSpacetimeFieldCore
import KGCoreCCR
import KGBosonicCreationCommutation
import KGBosonicAnnihilationCommutation

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

def fieldCommutatorCoefficient (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ)) : ℂ :=
  (s : ℂ)^2 *
    (inner ℂ (oneParticleSchwartzToHilbert a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)))
      (oneParticleSchwartzToHilbert a (spacetimeSmearingCLM a k)) -
     inner ℂ (oneParticleSchwartzToHilbert a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)))
      (oneParticleSchwartzToHilbert a (spacetimeSmearingCLM a h)))

theorem spacetimeFieldCore_CCR (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ)) :
    (spacetimeFieldCore a s h).comp (spacetimeFieldCore a s k) =
      (spacetimeFieldCore a s k).comp (spacetimeFieldCore a s h) +
        fieldCommutatorCoefficient a s h k • LinearMap.id := by
  apply LinearMap.ext
  intro v
  let H := spacetimeSmearingCLM a h
  let K := spacetimeSmearingCLM a k
  let Hc := spacetimeSmearingCLM a (conjugateSchwartzCLM h)
  let Kc := spacetimeSmearingCLM a (conjugateSchwartzCLM k)
  have hm1 := congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L v)
    (mixed_CCR_core a Hc K)
  have hm2 := congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L v)
    (mixed_CCR_core a Kc H)
  have hc := congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L v)
    (creationCore_commute H K)
  have ha := congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L v)
    (annihilationCore_commute a Hc Kc)
  change annihilationCore a Hc (creationCore K v) =
    inner ℂ (oneParticleSchwartzToHilbert a Hc) (oneParticleSchwartzToHilbert a K) • v +
      creationCore K (annihilationCore a Hc v) at hm1
  change annihilationCore a Kc (creationCore H v) =
    inner ℂ (oneParticleSchwartzToHilbert a Kc) (oneParticleSchwartzToHilbert a H) • v +
      creationCore H (annihilationCore a Kc v) at hm2
  change creationCore H (creationCore K v) = creationCore K (creationCore H v) at hc
  change annihilationCore a Hc (annihilationCore a Kc v) =
    annihilationCore a Kc (annihilationCore a Hc v) at ha
  simp only [spacetimeFieldCore, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, map_smul, map_add, LinearMap.id_coe, id_eq]
  rw [hm1, hm2, hc, ha]
  dsimp [fieldCommutatorCoefficient, H, K, Hc, Kc] at *
  have hsmap : algebraMap ℝ ℂ s = (s : ℂ) := rfl
  match_scalars <;> simp only [hsmap] <;> ring

end AASCKleinGordon
