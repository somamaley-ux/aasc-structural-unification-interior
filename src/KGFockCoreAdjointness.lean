import KGBosonicAdjointness
import KGCoreFieldOperations

noncomputable section
set_option maxHeartbeats 2000000
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem creation_annihilation_original_core_inner (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (creationCore f u)) (finiteParticleCoreToFock a v) =
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (annihilationCore a f v)) := by
  classical
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero, inner_zero_left]
  | add x y hx hy => simp only [map_add, inner_add_left, hx, hy]
  | of n H =>
      induction v using DirectSum.induction_on with
      | zero => simp only [map_zero, inner_zero_right]
      | add x y hx hy => simp only [map_add, inner_add_right, hx, hy]
      | of m K =>
          change inner ℂ (finiteParticleCoreToFock a (creationCore f
              (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)))
              (finiteParticleCoreToFock a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) m K)) =
            inner ℂ (finiteParticleCoreToFock a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
              (finiteParticleCoreToFock a (annihilationCore a f
                (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) m K)))
          cases m with
          | zero =>
              simp only [creationCore_lof, annihilationCore_lof_zero, map_zero,
                finiteParticleCoreToFock_on_sector, inner_zero_right, lp.inner_single_left]
              simp [lp.single_apply]
          | succ m =>
              simp only [creationCore_lof, annihilationCore_lof_succ, finiteParticleCoreToFock_on_sector]
              by_cases h : m = n
              · subst m
                simp only [lp.inner_single_left, lp.single_apply, Pi.single_eq_same]
                exact creation_annihilation_sector_adjoint a n f H K
              · have h' : m+1 ≠ n+1 := by omega
                simp [lp.inner_single_left, lp.single_apply, Pi.single_eq_of_ne h,
                  Pi.single_eq_of_ne h', h, Ne.symm h, h', Ne.symm h']

theorem fockCore_creation_annihilation_adjoint (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (u v : fockCoreDomain a) :
    inner ℂ (fockCoreCreation a f u) v.val = inner ℂ u.val (fockCoreAnnihilation a f v) := by
  let x := (fockCoreDomainEquiv a).symm u
  let y := (fockCoreDomainEquiv a).symm v
  have hu : u = includedFockCore a x := ((fockCoreDomainEquiv a).apply_symm_apply u).symm
  have hv : v = includedFockCore a y := ((fockCoreDomainEquiv a).apply_symm_apply v).symm
  rw [hu, hv, fockCoreCreation_on_original_core, fockCoreAnnihilation_on_original_core]
  exact creation_annihilation_original_core_inner a f x y

end AASCKleinGordon
