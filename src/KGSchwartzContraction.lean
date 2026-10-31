import KGSchwartzCoordinates
import SchwartzWeightedIntegral
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option

noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

def liftParticlePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv n).trans ((Equiv.optionCongr σ).trans (finSuccEquiv n).symm)

@[simp] theorem liftParticlePermutation_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    liftParticlePermutation σ 0 = 0 := by simp [liftParticlePermutation]

@[simp] theorem liftParticlePermutation_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    liftParticlePermutation σ i.succ = (σ i).succ := by simp [liftParticlePermutation]

theorem cons_permuted_tail {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Momentum)
    (y : ParticleConfiguration n) :
    Fin.cons p (fun i => y (σ i)) = fun i =>
      Fin.cons (α:=fun _ : Fin (n+1) => Momentum) p y (liftParticlePermutation σ i) := by
  ext i
  cases i using Fin.cases <;> simp

def particleContractionCLM (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ)) :
    𝓢(ParticleConfiguration (n+1),ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  (weightedPartialIntegralCLM (μ:=wignerMeasure a)
    ((postcomposeCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f).integrable)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (joinParticleCoordinates n))

@[simp] theorem particleContractionCLM_apply (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration (n+1),ℂ)) (y : ParticleConfiguration n) :
    particleContractionCLM a n f H y = ∫ p, star (f p) * H (Fin.cons p y) ∂wignerMeasure a := rfl

theorem particleContractionCLM_bosonic (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz (n+1)) : particleContractionCLM a n f H.val ∈ bosonicSchwartz n := by
  intro σ y
  simp only [particleContractionCLM_apply]
  apply integral_congr_ae
  exact ae_of_all (wignerMeasure a) fun p => by
    change star (f p) * H.val (Fin.cons p (fun i => y (σ i))) =
      star (f p) * H.val (Fin.cons p y)
    rw [cons_permuted_tail]
    rw [H.property (liftParticlePermutation σ) (Fin.cons p y)]

def annihilationSectorCLM (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ)) :
    bosonicSchwartz (n+1) →L[ℂ] bosonicSchwartz n :=
  (((Real.sqrt (n+1) : ℂ) • particleContractionCLM a n f).comp
    (bosonicSchwartz (n+1)).subtypeL).codRestrict (bosonicSchwartz n) (by
      intro H
      exact (bosonicSchwartz n).smul_mem _ (particleContractionCLM_bosonic a n f H))

theorem annihilationSectorCLM_apply (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz (n+1)) (y : ParticleConfiguration n) :
    (annihilationSectorCLM a n f H).val y = (Real.sqrt (n+1) : ℂ) *
      ∫ p, star (f p) * H.val (Fin.cons p y) ∂wignerMeasure a := rfl

theorem particleContraction_tensorInsert (a : Parameters) (n : ℕ) (f g : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    particleContractionCLM a n f (particleTensorInsertCLM n g H) =
      (∫ p, star (f p) * g p ∂wignerMeasure a) • H := by
  ext y
  simp only [particleContractionCLM_apply, particleTensorInsertCLM_apply,
    Fin.cons_zero, Fin.tail_cons, SchwartzMap.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  exact integral_mul_const _ _

end AASCKleinGordon
