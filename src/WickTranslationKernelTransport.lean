import WickPoincarePairTransport

noncomputable section
set_option maxHeartbeats 1500000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_core_event_component (a : Parameters) (b : Spacetime)
    (u : FiniteParticleCore) (n : ℕ) (z : ParticleConfiguration n) :
    ((coreEventTranslation a b u) n).val z =
      particleEventTranslationPhase a n b z * (u n).val z :=
  bosonicEventTranslationSchwartz_apply a n b (u n) z

theorem wick_particle_phase_cons (a : Parameters) (b : Spacetime) (n : ℕ)
    (p : Momentum) (z : ParticleConfiguration n) :
    particleEventTranslationPhase a (n+1) b (Fin.cons p z) =
      eventTranslationPhase a b p * particleEventTranslationPhase a n b z := by
  simp only [particleEventTranslationPhase, particleEventMomentum, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, translationPhase_add_value, eventTranslationPhase]

theorem wick_unit_phase_star_mul (z : ℂ) (unit : ‖z‖=1) : star z*z=1 := by
  have h := Complex.mul_conj' z
  rw [unit] at h
  simpa only [Complex.ofReal_one, one_pow, starRingEnd_apply, mul_comm] using h

theorem wick_event_AA_kernel (a : Parameters) (b : Spacetime) (n : ℕ)
    (u v : FiniteParticleCore) (z : ParticleConfiguration (n+2)) :
    wickAAStateKernel n ((coreEventTranslation a b u) n).val
      ((coreEventTranslation a b v) (n+2)).val z =
      eventTranslationPhase a b (z 0) * eventTranslationPhase a b (z 1) *
        wickAAStateKernel n (u n).val (v (n+2)).val z := by
  have decomp : z=Fin.cons (z 0) (Fin.cons (z 1) (Fin.tail (Fin.tail z))) := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases <;> rfl
  have phase : particleEventTranslationPhase a (n+2) b z =
      eventTranslationPhase a b (z 0) * (eventTranslationPhase a b (z 1) *
        particleEventTranslationPhase a n b (Fin.tail (Fin.tail z))) := by
    conv_lhs => rw [decomp]
    rw [wick_particle_phase_cons, wick_particle_phase_cons]
  simp only [wickAAStateKernel_apply, wick_core_event_component, star_mul]
  rw [phase]
  have cancel := wick_unit_phase_star_mul _
    (particleEventTranslationPhase_norm a n b (Fin.tail (Fin.tail z)))
  linear_combination
    (star ((u n).val (Fin.tail (Fin.tail z))) * eventTranslationPhase a b (z 0) *
      eventTranslationPhase a b (z 1) * (v (n+2)).val z) * cancel

theorem wick_event_mixed_kernel (a : Parameters) (b : Spacetime) (n : ℕ)
    (u v : FiniteParticleCore) (z : ParticleConfiguration (n+2)) :
    wickMixedStateKernel n ((coreEventTranslation a b u) (n+1)).val
      ((coreEventTranslation a b v) (n+1)).val z =
      star (eventTranslationPhase a b (z 0)) * eventTranslationPhase a b (z 1) *
        wickMixedStateKernel n (u (n+1)).val (v (n+1)).val z := by
  have tail : Fin.tail z=Fin.cons (z 1) (Fin.tail (Fin.tail z)) := by
    ext i
    cases i using Fin.cases <;> rfl
  simp only [wickMixedStateKernel_apply, wick_core_event_component, wick_particle_phase_cons]
  rw [tail, wick_particle_phase_cons]
  simp only [star_mul, ← tail]
  have cancel := wick_unit_phase_star_mul _
    (particleEventTranslationPhase_norm a n b (Fin.tail (Fin.tail z)))
  linear_combination
    (star (eventTranslationPhase a b (z 0)) * star ((u (n+1)).val
      (Fin.cons (z 0) (Fin.tail (Fin.tail z)))) * eventTranslationPhase a b (z 1) *
      (v (n+1)).val (Fin.tail z)) * cancel

end AASCKleinGordon
