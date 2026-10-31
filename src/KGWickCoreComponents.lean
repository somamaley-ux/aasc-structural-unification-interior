import KGOriginalWickChannels
import KGWickSectorAttachment

noncomputable section
set_option maxHeartbeats 3000000
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon
attribute [local instance] Classical.propDecidable

theorem wick_original_fock_component (a : Parameters) (v : FiniteParticleCore) (n : ℕ) :
    finiteParticleCoreToFock a v n = bosonicCoreToSector a n (v n) := by
  classical
  induction v using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add, lp.coeFn_add, Pi.add_apply,
      DirectSum.add_apply] using congrArg₂ (· + ·) hx hy
  | of m H =>
      change finiteParticleCoreToFock a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) m H) n = _
      rw [finiteParticleCoreToFock_on_sector]
      by_cases he : m=n
      · subst m
        simp [lp.single_apply, DirectSum.lof_eq_of, DirectSum.of_apply]
      · simp [lp.single_apply, DirectSum.lof_eq_of, DirectSum.of_apply, he, Ne.symm he]

theorem wick_original_annihilation_component (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (v : FiniteParticleCore) (n : ℕ) :
    annihilationCore a f v n = annihilationSectorCLM a n f (v (n+1)) := by
  classical
  induction v using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add, DirectSum.add_apply] using congrArg₂ (· + ·) hx hy
  | of m H =>
      change annihilationCore a f (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) m H) n = _
      cases m with
      | zero =>
          rw [annihilationCore_lof_zero]
          simp [DirectSum.lof_eq_of, DirectSum.of_apply]
      | succ m =>
          rw [annihilationCore_lof_succ]
          by_cases he : m=n
          · subst m
            simp [DirectSum.lof_eq_of, DirectSum.of_apply]
          · have hs : m+1≠n+1 := by omega
            simp [DirectSum.lof_eq_of, DirectSum.of_apply, he, Ne.symm he, hs, Ne.symm hs]

theorem wick_original_fock_inner_finite_sum (a : Parameters) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v) =
      ∑ n ∈ u.support, inner ℂ (bosonicCoreToSector a n (u n))
        (bosonicCoreToSector a n (v n)) := by
  classical
  rw [lp.inner_eq_tsum]
  simp_rw [wick_original_fock_component]
  apply tsum_eq_sum
  intro n hn
  have hu : u n = 0 := DFinsupp.notMem_support_iff.mp hn
  simp [hu]

end AASCKleinGordon
