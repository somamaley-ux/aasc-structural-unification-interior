import KGSpacetimeTranslationUnitary
import KGTemporalShellCoefficients
import KGOriginalShellCausalSupport

noncomputable section
set_option maxHeartbeats 1600000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem eventMomentumPair_temperate (a : Parameters) (b : Spacetime) :
    (eventMomentumPair a b).HasTemperateGrowth :=
  (innerSL ℝ b).hasTemperateGrowth.comp (shellCovector_temperate a)

theorem particleEventMomentum_temperate (a : Parameters) (n : ℕ) (b : Spacetime) :
    (particleEventMomentum a n b).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.sum
  intro i _
  exact (eventMomentumPair_temperate a b).comp
    (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum).hasTemperateGrowth

theorem translationPhase_temperate (hbar t : ℝ) : (Translation.phase hbar t).HasTemperateGrowth := by
  have ha : (fun r : ℝ => -t*r/hbar).HasTemperateGrowth := by
    simp only [div_eq_mul_inv]
    fun_prop
  have he : Translation.phase hbar t=(fun r : ℝ =>
      (Real.cos (-t*r/hbar) : ℂ)+(Real.sin (-t*r/hbar) : ℂ)*Complex.I) := by
    funext r
    rw [Translation.phase,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
  rw [he]
  exact (Complex.ofRealCLM.hasTemperateGrowth.comp (real_cos_temperate.comp ha)).add
    ((Complex.ofRealCLM.hasTemperateGrowth.comp (real_sin_temperate.comp ha)).mul
      (Function.HasTemperateGrowth.const Complex.I))

def eventTranslationPhase (a : Parameters) (b : Spacetime) (p : Momentum) : ℂ :=
  Translation.phase a.hbar 1 (eventMomentumPair a b p)

def particleEventTranslationPhase (a : Parameters) (n : ℕ) (b : Spacetime)
    (x : ParticleConfiguration n) : ℂ := Translation.phase a.hbar 1 (particleEventMomentum a n b x)

theorem eventTranslationPhase_temperate (a : Parameters) (b : Spacetime) :
    (eventTranslationPhase a b).HasTemperateGrowth :=
  (translationPhase_temperate a.hbar 1).comp (eventMomentumPair_temperate a b)

theorem particleEventTranslationPhase_temperate (a : Parameters) (n : ℕ) (b : Spacetime) :
    (particleEventTranslationPhase a n b).HasTemperateGrowth :=
  (translationPhase_temperate a.hbar 1).comp (particleEventMomentum_temperate a n b)

theorem eventTranslationPhase_norm (a : Parameters) (b : Spacetime) (p : Momentum) :
    ‖eventTranslationPhase a b p‖=1 := Translation.phase_norm _ _ _

theorem particleEventTranslationPhase_norm (a : Parameters) (n : ℕ) (b : Spacetime)
    (x : ParticleConfiguration n) : ‖particleEventTranslationPhase a n b x‖=1 :=
  Translation.phase_norm _ _ _

theorem particleEventTranslationPhase_permutation (a : Parameters) (n : ℕ) (b : Spacetime)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleEventTranslationPhase a n b (particlePermutation n σ x)=particleEventTranslationPhase a n b x := by
  unfold particleEventTranslationPhase
  rw [particleEventMomentum_permutation]

def eventTranslationSchwartzCLM (a : Parameters) (b : Spacetime) :
    𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (eventTranslationPhase a b)

def particleEventTranslationSchwartzCLM (a : Parameters) (n : ℕ) (b : Spacetime) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (particleEventTranslationPhase a n b)

theorem eventTranslationSchwartz_apply (a : Parameters) (b : Spacetime)
    (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    eventTranslationSchwartzCLM a b f p=eventTranslationPhase a b p*f p :=
  SchwartzMap.smulLeftCLM_apply_apply (eventTranslationPhase_temperate a b) f p

theorem particleEventTranslationSchwartz_apply (a : Parameters) (n : ℕ) (b : Spacetime)
    (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    particleEventTranslationSchwartzCLM a n b f x=particleEventTranslationPhase a n b x*f x :=
  SchwartzMap.smulLeftCLM_apply_apply (particleEventTranslationPhase_temperate a n b) f x

theorem particleEventTranslationPhase_add (a : Parameters) (n : ℕ) (b d : Spacetime)
    (x : ParticleConfiguration n) :
    particleEventTranslationPhase a n (b+d) x=
      particleEventTranslationPhase a n b x*particleEventTranslationPhase a n d x := by
  simp only [particleEventTranslationPhase,particleEventMomentum_add,translationPhase_add_value]

theorem particleEventTranslationPhase_zero (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleEventTranslationPhase a n 0 x=1 := by
  simp [particleEventTranslationPhase,particleEventMomentum_zero,Translation.phase]

end AASCKleinGordon
