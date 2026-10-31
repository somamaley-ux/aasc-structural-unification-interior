import KGOriginalCoreEventTranslation
import KGAxisBoostFieldOperations
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 2000000
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem particleEventMomentum_swapDelete (a : Parameters) (n : ℕ) (b : Spacetime)
    (i : Fin (n+1)) (x : ParticleConfiguration (n+1)) :
    particleEventMomentum a (n+1) b x=
      eventMomentumPair a b (x i)+particleEventMomentum a n b (swapDelete n i x) := by
  unfold particleEventMomentum swapDelete
  have he := Equiv.sum_comp (Equiv.swap (0 : Fin (n+1)) i)
    (fun j : Fin (n+1) => eventMomentumPair a b (x j))
  simpa only [Fin.sum_univ_succ,Equiv.swap_apply_left] using he.symm

theorem particleEventTranslationPhase_swapDelete (a : Parameters) (n : ℕ) (b : Spacetime)
    (i : Fin (n+1)) (x : ParticleConfiguration (n+1)) :
    particleEventTranslationPhase a (n+1) b x=
      eventTranslationPhase a b (x i)*particleEventTranslationPhase a n b (swapDelete n i x) := by
  unfold particleEventTranslationPhase eventTranslationPhase
  rw [particleEventMomentum_swapDelete,translationPhase_add_value]

theorem eventTranslation_creationSector (a : Parameters) (n : ℕ) (b : Spacetime)
    (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    bosonicEventTranslationSchwartzCLM a (n+1) b (creationSectorCLM n f H)=
      creationSectorCLM n (eventTranslationSchwartzCLM a b f)
        (bosonicEventTranslationSchwartzCLM a n b H) := by
  apply Subtype.ext
  ext x
  rw [bosonicEventTranslationSchwartz_apply]
  simp only [creationSectorCLM_apply,SchwartzMap.smul_apply,smul_eq_mul,symmetrizer_insert_apply,
    eventTranslationSchwartz_apply,bosonicEventTranslationSchwartz_apply]
  have hs : particleEventTranslationPhase a (n+1) b x*
      (∑ i : Fin (n+1),f (x i)*H.val (swapDelete n i x))=
      ∑ i : Fin (n+1),(eventTranslationPhase a b (x i)*f (x i))*
        (particleEventTranslationPhase a n b (swapDelete n i x)*H.val (swapDelete n i x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [particleEventTranslationPhase_swapDelete a n b i x]
    ring
  simp only [Nat.cast_add,Nat.cast_one,add_comm (n : ℂ) 1]
  linear_combination (Real.sqrt (n+1) : ℂ)*((1+(n : ℂ))⁻¹)*hs

theorem eventTranslation_creationCore (a : Parameters) (b : Spacetime)
    (f : 𝓢(Momentum,ℂ)) (u : FiniteParticleCore) :
    coreEventTranslation a b (creationCore f u)=
      creationCore (eventTranslationSchwartzCLM a b f) (coreEventTranslation a b u) := by
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
    change coreEventTranslation a b (creationCore f
      (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))=
      creationCore (eventTranslationSchwartzCLM a b f) (coreEventTranslation a b
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
    rw [creationCore_lof,coreEventTranslation_lof,coreEventTranslation_lof,creationCore_lof,
      eventTranslation_creationSector]

theorem eventTranslation_annihilationCore (a : Parameters) (b : Spacetime)
    (f : 𝓢(Momentum,ℂ)) (v : FiniteParticleCore) :
    coreEventTranslation a b (annihilationCore a f v)=
      annihilationCore a (eventTranslationSchwartzCLM a b f) (coreEventTranslation a b v) := by
  apply original_core_inner_ext a
  intro w
  let u := coreEventTranslation a (-b) w
  have hu : coreEventTranslation a b u=w := by
    simpa only [u,neg_neg] using coreEventTranslation_inverse a (-b) w
  calc
    inner ℂ (finiteParticleCoreToFock a w)
        (finiteParticleCoreToFock a (coreEventTranslation a b (annihilationCore a f v)))=
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (annihilationCore a f v)) := by
        rw [← hu,coreEventTranslation_preserves_inner]
    _ = inner ℂ (finiteParticleCoreToFock a (creationCore f u))
        (finiteParticleCoreToFock a v) := (creation_annihilation_original_core_inner a f u v).symm
    _ = inner ℂ (finiteParticleCoreToFock a (coreEventTranslation a b (creationCore f u)))
        (finiteParticleCoreToFock a (coreEventTranslation a b v)) :=
      (coreEventTranslation_preserves_inner a b _ _).symm
    _ = inner ℂ (finiteParticleCoreToFock a w)
        (finiteParticleCoreToFock a (annihilationCore a (eventTranslationSchwartzCLM a b f)
          (coreEventTranslation a b v))) := by
        rw [eventTranslation_creationCore,creation_annihilation_original_core_inner,hu]

end AASCKleinGordon
