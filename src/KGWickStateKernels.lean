import KGParticleAdjointness
import SchwartzConjugation

/-! State coefficients for the original two-particle Wick channels. The mixed
coefficient uses the full entangled wavefunctions with shared spectators.
Injectivity of the state-coordinate embedding supplies the Schwartz estimate;
no properness of a shell-momentum difference map is asserted. -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

def wickStatePullback {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : D →L[ℝ] E) (hi : Function.Injective L) :
    𝓢(E,ℂ) →L[ℂ] 𝓢(D,ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ L.hasTemperateGrowth
    (((L.toLinearMap.injective_iff_antilipschitz).mp hi).choose_spec.2)

@[simp] theorem wickStatePullback_apply {D E : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : D →L[ℝ] E) (hi : Function.Injective L)
    (f : 𝓢(E,ℂ)) (z : D) : wickStatePullback L hi f z = f (L z) := rfl

def wickMixedEmbedding (n : ℕ) : ParticleConfiguration (n+2) →L[ℝ]
    ParticleConfiguration (n+1) × ParticleConfiguration (n+1) :=
  ( { toFun := fun z => (Fin.cons (z 0) (Fin.tail (Fin.tail z)), Fin.tail z)
      map_add' := by
        intro z w
        apply Prod.ext
        · ext i
          cases i using Fin.cases <;> rfl
        · rfl
      map_smul' := by
        intro c z
        apply Prod.ext
        · ext i
          cases i using Fin.cases <;> rfl
        · rfl } : ParticleConfiguration (n+2) →ₗ[ℝ]
          ParticleConfiguration (n+1) × ParticleConfiguration (n+1)).toContinuousLinearMap

theorem wickMixedEmbedding_injective (n : ℕ) : Function.Injective (wickMixedEmbedding n) := by
  intro z w eq
  have hfirst := congrArg (fun t => t.1 0) eq
  have htail := congrArg Prod.snd eq
  change z 0 = w 0 at hfirst
  change Fin.tail z = Fin.tail w at htail
  funext i
  cases i using Fin.cases with
  | zero => exact hfirst
  | succ i => exact congrFun htail i

def wickAAEmbedding (n : ℕ) : ParticleConfiguration (n+2) →L[ℝ]
    ParticleConfiguration n × ParticleConfiguration (n+2) :=
  ( { toFun := fun z => (Fin.tail (Fin.tail z), z)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } : ParticleConfiguration (n+2) →ₗ[ℝ]
          ParticleConfiguration n × ParticleConfiguration (n+2)).toContinuousLinearMap

theorem wickAAEmbedding_injective (n : ℕ) : Function.Injective (wickAAEmbedding n) := by
  intro z w h
  exact congrArg Prod.snd h

def wickMixedStateKernel (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) : 𝓢(ParticleConfiguration (n+2),ℂ) :=
  wickStatePullback (wickMixedEmbedding n) (wickMixedEmbedding_injective n)
    (tensorLeftCLM (conjugateSchwartzCLM u) v)

@[simp] theorem wickMixedStateKernel_apply (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) (z : ParticleConfiguration (n+2)) :
    wickMixedStateKernel n u v z =
      star (u (Fin.cons (z 0) (Fin.tail (Fin.tail z)))) * v (Fin.tail z) := by
  rw [wickMixedStateKernel, wickStatePullback_apply]
  rfl

def wickAAStateKernel (n : ℕ) (u : 𝓢(ParticleConfiguration n,ℂ))
    (v : 𝓢(ParticleConfiguration (n+2),ℂ)) : 𝓢(ParticleConfiguration (n+2),ℂ) :=
  wickStatePullback (wickAAEmbedding n) (wickAAEmbedding_injective n)
    (tensorLeftCLM (conjugateSchwartzCLM u) v)

@[simp] theorem wickAAStateKernel_apply (n : ℕ) (u : 𝓢(ParticleConfiguration n,ℂ))
    (v : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2)) :
    wickAAStateKernel n u v z = star (u (Fin.tail (Fin.tail z))) * v z := by
  rw [wickAAStateKernel, wickStatePullback_apply]
  rfl

theorem wickMixedStateKernel_integrable (a : Parameters) (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) :
    Integrable (wickMixedStateKernel n u v) (particleMeasure a (n+2)) :=
  (wickMixedStateKernel n u v).integrable

theorem wickAAStateKernel_integrable (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    Integrable (wickAAStateKernel n u v) (particleMeasure a (n+2)) :=
  (wickAAStateKernel n u v).integrable

theorem wickMixedStateKernel_all_moments (a : Parameters) (n k : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) :
    Integrable (fun z => ‖z‖^k * ‖wickMixedStateKernel n u v z‖)
      (particleMeasure a (n+2)) :=
  (wickMixedStateKernel n u v).integrable_pow_mul _ k

theorem wickAAStateKernel_all_moments (a : Parameters) (n k : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    Integrable (fun z => ‖z‖^k * ‖wickAAStateKernel n u v z‖)
      (particleMeasure a (n+2)) :=
  (wickAAStateKernel n u v).integrable_pow_mul _ k

end AASCKleinGordon
