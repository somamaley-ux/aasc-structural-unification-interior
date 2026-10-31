import KGSchwartzSymmetrization
import SchwartzTensorInsertion
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

def joinParticleCoordinates (n : ℕ) : (Momentum × ParticleConfiguration n) ≃L[ℝ]
    ParticleConfiguration (n+1) :=
  ({ toEquiv := Fin.consEquiv (fun _ : Fin (n+1) => Momentum)
     map_add' := by
       intro x y
       ext i
       cases i using Fin.cases <;> rfl
     map_smul' := by
       intro c x
       ext i
       cases i using Fin.cases <;> rfl } :
    (Momentum × ParticleConfiguration n) ≃ₗ[ℝ] ParticleConfiguration (n+1)).toContinuousLinearEquiv

@[simp] theorem joinParticleCoordinates_apply (n : ℕ) (p : Momentum) (y : ParticleConfiguration n) :
    joinParticleCoordinates n (p,y) = Fin.cons p y := rfl

@[simp] theorem joinParticleCoordinates_symm_apply (n : ℕ) (y : ParticleConfiguration (n+1)) :
    (joinParticleCoordinates n).symm y = (y 0,Fin.tail y) := rfl

def particleTensorInsertCLM (n : ℕ) (f : 𝓢(Momentum,ℂ)) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration (n+1),ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (joinParticleCoordinates n).symm).comp
    (tensorLeftCLM f)

@[simp] theorem particleTensorInsertCLM_apply (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration n,ℂ)) (y : ParticleConfiguration (n+1)) :
    particleTensorInsertCLM n f H y = f (y 0) * H (Fin.tail y) := rfl

def creationSectorCLM (n : ℕ) (f : 𝓢(Momentum,ℂ)) :
    bosonicSchwartz n →L[ℂ] bosonicSchwartz (n+1) :=
  ((Real.sqrt (n+1) : ℂ) •
    ((schwartzSymmetrizer (n+1)).comp (particleTensorInsertCLM n f))).codRestrict
      (bosonicSchwartz (n+1)) (by
        intro H
        exact (bosonicSchwartz (n+1)).smul_mem _ (schwartzSymmetrizer_bosonic (n+1) _)) |>.comp
    (bosonicSchwartz n).subtypeL

theorem creationSectorCLM_apply (n : ℕ) (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    (creationSectorCLM n f H).val = (Real.sqrt (n+1) : ℂ) •
      schwartzSymmetrizer (n+1) (particleTensorInsertCLM n f H.val) := rfl

end AASCKleinGordon
