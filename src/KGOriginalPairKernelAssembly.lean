import KGWickFiniteCoreKernelAttachment

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

def wickAASmearedCoreKernel (a : Parameters) (f g : 𝓢(Momentum,ℂ))
    (u v : FiniteParticleCore) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ)) *
    ∫ z, star (g (z 0)) * star (f (z 1)) *
      wickAAStateKernel n (u n).val (v (n+2)).val z ∂particleMeasure a (n+2)

def wickMixedSmearedCoreKernel (a : Parameters) (f g : 𝓢(Momentum,ℂ))
    (u v : FiniteParticleCore) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ((n+1 : ℝ) : ℂ) *
    ∫ z, f (z 0) * star (g (z 1)) *
      wickMixedStateKernel n (u (n+1)).val (v (n+1)).val z ∂particleMeasure a (n+2)

def wickJointCoreCutoff (u v : FiniteParticleCore) : ℕ :=
  max (wickCoreCutoff u) (wickCoreCutoff v)

theorem originalPairForm_eq_original_core_wick_kernels (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    let N := wickJointCoreCutoff u v
    originalPairForm a s h k u v = (s : ℂ)^2 *
      (star (wickAASmearedCoreKernel a (spacetimeSmearingCLM a k)
          (spacetimeSmearingCLM a h) v u N) +
       wickMixedSmearedCoreKernel a (spacetimeSmearingCLM a h)
          (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) u v N +
       wickMixedSmearedCoreKernel a (spacetimeSmearingCLM a k)
          (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) u v N +
       wickAASmearedCoreKernel a (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
          (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) u v N) := by
  dsimp only
  let N := wickJointCoreCutoff u v
  have hu : ∀ n,N≤n → u n=0 := by
    intro n hn
    exact wickCoreCutoff_zero u n ((le_max_left _ _).trans hn)
  have hv : ∀ n,N≤n → v n=0 := by
    intro n hn
    exact wickCoreCutoff_zero v n ((le_max_right _ _).trans hn)
  have haa (f g : 𝓢(Momentum,ℂ)) :
      inner ℂ (finiteParticleCoreToFock a u)
        (finiteParticleCoreToFock a (annihilationCore a f (annihilationCore a g v))) =
      wickAASmearedCoreKernel a f g u v N :=
    wickAA_original_core_kernel_attachment a f g u v N hu
  have hcc (f g : 𝓢(Momentum,ℂ)) :
      inner ℂ (finiteParticleCoreToFock a (annihilationCore a f (annihilationCore a g u)))
        (finiteParticleCoreToFock a v) = star (wickAASmearedCoreKernel a f g v u N) := by
    unfold wickAASmearedCoreKernel
    rw [← wickAA_original_core_kernel_attachment a f g v u N hv]
    exact (inner_conj_symm _ _).symm
  have hm (f g : 𝓢(Momentum,ℂ)) :
      inner ℂ (finiteParticleCoreToFock a (annihilationCore a f u))
        (finiteParticleCoreToFock a (annihilationCore a g v)) =
      wickMixedSmearedCoreKernel a f g u v N :=
    wickMixed_original_core_kernel_attachment a f g u v N hu
  rw [originalPairForm_contraction_channels, hcc, hm, hm, haa]

end AASCKleinGordon
