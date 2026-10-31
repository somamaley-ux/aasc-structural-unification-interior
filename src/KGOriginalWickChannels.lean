import KGOriginalPairPolarization

/-! Exact normal-order decomposition of the ORIGINAL bilocal pair on its
original finite-particle Schwartz core. Amplitude and complex conjugations
are retained. No coincident-point restriction is asserted here. -/
noncomputable section
set_option maxHeartbeats 3000000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem normalOrderedFieldPairCore_four_channels (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    normalOrderedFieldPairCore a s h k = (s : ℂ)^2 •
      ((creationCore (spacetimeSmearingCLM a h)).comp
          (creationCore (spacetimeSmearingCLM a k)) +
       (creationCore (spacetimeSmearingCLM a h)).comp
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k))) +
       (creationCore (spacetimeSmearingCLM a k)).comp
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h))) +
       (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h))).comp
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)))) := by
  rw [normalOrderedFieldPairCore]
  simp only [spacetimeFieldCore, LinearMap.smul_comp, LinearMap.comp_smul,
    LinearMap.add_comp, LinearMap.comp_add]
  rw [mixed_CCR_core, ← massShellTwoPointPairing_eq_inner]
  module

theorem originalPairForm_four_channels (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    originalPairForm a s h k u v = (s : ℂ)^2 *
      (inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a
          (creationCore (spacetimeSmearingCLM a h)
            (creationCore (spacetimeSmearingCLM a k) v))) +
       inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a
          (creationCore (spacetimeSmearingCLM a h)
            (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v))) +
       inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a
          (creationCore (spacetimeSmearingCLM a k)
            (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) v))) +
       inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
            (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v)))) := by
  rw [originalPairForm, normalOrderedFieldPairCore_four_channels]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_smul, map_add, inner_smul_right, inner_add_right]

theorem originalPairForm_contraction_channels (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    originalPairForm a s h k u v = (s : ℂ)^2 *
      (inner ℂ
        (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a k)
            (annihilationCore a (spacetimeSmearingCLM a h) u)))
        (finiteParticleCoreToFock a v) +
       inner ℂ (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a h) u))
        (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v)) +
       inner ℂ (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a k) u))
        (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) v)) +
       inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
            (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v)))) := by
  rw [originalPairForm_four_channels]
  rw [← annihilation_creation_original_core_inner a (spacetimeSmearingCLM a h) u
      (creationCore (spacetimeSmearingCLM a k) v),
    ← annihilation_creation_original_core_inner a (spacetimeSmearingCLM a k)
      (annihilationCore a (spacetimeSmearingCLM a h) u) v,
    ← annihilation_creation_original_core_inner a (spacetimeSmearingCLM a h) u
      (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v),
    ← annihilation_creation_original_core_inner a (spacetimeSmearingCLM a k) u
      (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) v)]

end AASCKleinGordon
