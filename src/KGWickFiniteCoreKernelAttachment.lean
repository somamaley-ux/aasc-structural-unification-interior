import KGWickCoreComponents
import KGWickMixedAttachment

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon
attribute [local instance] Classical.propDecidable

def wickCoreCutoff (v : FiniteParticleCore) : ℕ := v.support.sup id + 1

theorem wickCoreCutoff_zero (v : FiniteParticleCore) (n : ℕ) (hn : wickCoreCutoff v ≤ n) :
    v n = 0 := by
  by_contra h
  have hs := Finset.le_sup (f:=id) (DFinsupp.mem_support_iff.mpr h)
  change n ≤ v.support.sup id at hs
  unfold wickCoreCutoff at hn
  omega

theorem wick_original_fock_inner_range (a : Parameters) (u v : FiniteParticleCore)
    (N : ℕ) (hu : ∀ n,N≤n → u n=0) :
    inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v) =
      ∑ n ∈ Finset.range N, inner ℂ (bosonicCoreToSector a n (u n))
        (bosonicCoreToSector a n (v n)) := by
  rw [lp.inner_eq_tsum]
  simp_rw [wick_original_fock_component]
  apply tsum_eq_sum
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  simp [hu n hn]

theorem wickAA_original_core_kernel_attachment (a : Parameters) (f g : 𝓢(Momentum,ℂ))
    (u v : FiniteParticleCore) (N : ℕ) (hu : ∀ n,N≤n → u n=0) :
    inner ℂ (finiteParticleCoreToFock a u)
      (finiteParticleCoreToFock a (annihilationCore a f (annihilationCore a g v))) =
      ∑ n ∈ Finset.range N,
        ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ)) *
          ∫ z, star (g (z 0)) * star (f (z 1)) *
            wickAAStateKernel n (u n).val (v (n+2)).val z ∂particleMeasure a (n+2) := by
  rw [wick_original_fock_inner_range a u _ N hu]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [wick_original_annihilation_component]
  exact wickAA_kernel_eq_original_bosonic_annihilations a n f g (u n) (v (n+2))

theorem wickMixed_original_core_kernel_attachment (a : Parameters) (f g : 𝓢(Momentum,ℂ))
    (u v : FiniteParticleCore) (N : ℕ) (hu : ∀ n,N≤n → u n=0) :
    inner ℂ (finiteParticleCoreToFock a (annihilationCore a f u))
      (finiteParticleCoreToFock a (annihilationCore a g v)) =
      ∑ n ∈ Finset.range N, ((n+1 : ℝ) : ℂ) *
        ∫ z, f (z 0) * star (g (z 1)) *
          wickMixedStateKernel n (u (n+1)).val (v (n+1)).val z ∂particleMeasure a (n+2) := by
  have hAu : ∀ n,N≤n → annihilationCore a f u n=0 := by
    intro n hn
    rw [wick_original_annihilation_component, hu (n+1) (by omega), map_zero]
  rw [wick_original_fock_inner_range a _ _ N hAu]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [wick_original_annihilation_component]
  exact wickMixed_kernel_eq_original_bosonic_annihilations a n f g (u (n+1)) (v (n+1))

end AASCKleinGordon
