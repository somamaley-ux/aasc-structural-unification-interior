import KGCoreTopologyRepresentation
import KGSchwartzSmearingLaws

noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon
open SchwartzOperations

def tensorRightCLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : 𝓢(F,ℂ)) :
    𝓢(E,ℂ) →L[ℂ] 𝓢(E × F,ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ E F)).comp
    (tensorLeftCLM H)

def particleInsertionSmearCLM (n : ℕ) (H : 𝓢(ParticleConfiguration n,ℂ)) :
    𝓢(Momentum,ℂ) →L[ℂ] 𝓢(ParticleConfiguration (n+1),ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (joinParticleCoordinates n).symm).comp
    (tensorRightCLM H)

theorem particleInsertionSmearCLM_apply (n : ℕ) (H : 𝓢(ParticleConfiguration n,ℂ))
    (f : 𝓢(Momentum,ℂ)) : particleInsertionSmearCLM n H f = particleTensorInsertCLM n f H := by
  ext y
  change H (Fin.tail y) * f (y 0) = f (y 0) * H (Fin.tail y)
  ring

def creationSectorSmearCLM (n : ℕ) (H : bosonicSchwartz n) :
    𝓢(Momentum,ℂ) →L[ℂ] bosonicSchwartz (n+1) :=
  ((Real.sqrt (n+1) : ℂ) • ((schwartzSymmetrizer (n+1)).comp
    (particleInsertionSmearCLM n H.val))).codRestrict (bosonicSchwartz (n+1)) (by
      intro f
      exact (bosonicSchwartz (n+1)).smul_mem _ (schwartzSymmetrizer_bosonic (n+1) _))

theorem creationSectorSmearCLM_apply (n : ℕ) (H : bosonicSchwartz n) (f : 𝓢(Momentum,ℂ)) :
    creationSectorSmearCLM n H f = creationSectorCLM n f H := by
  apply Subtype.ext
  change (Real.sqrt (n+1) : ℂ) • schwartzSymmetrizer (n+1) (particleInsertionSmearCLM n H.val f) = _
  rw [particleInsertionSmearCLM_apply]
  rfl

theorem creationCore_smearing_continuous (v : FiniteParticleCore) :
    Continuous (fun f : 𝓢(Momentum,ℂ) => creationCore f v) := by
  induction v using DirectSum.induction_on with
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : 𝓢(Momentum,ℂ) => (0 : FiniteParticleCore)))
  | add x y hx hy => simpa only [map_add] using hx.add hy
  | of n H =>
      change Continuous (fun f : 𝓢(Momentum,ℂ) => creationCore f
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
      simp_rw [creationCore_lof, ← creationSectorSmearCLM_apply]
      exact (finiteParticleCore_lof_continuous (n+1)).comp (creationSectorSmearCLM n H).continuous

def coreCreationSmearCLM (v : FiniteParticleCore) : 𝓢(Momentum,ℂ) →L[ℂ] FiniteParticleCore where
  toFun f := creationCore f v
  map_add' f g := by rw [creationCore_add_smear]; rfl
  map_smul' c f := by rw [creationCore_smul_smear]; rfl
  cont := creationCore_smearing_continuous v

def fockCreationSmearCLM (a : Parameters) (v : FiniteParticleCore) :
    𝓢(Momentum,ℂ) →L[ℂ] FockHilbert a :=
  ({ toLinearMap := finiteParticleCoreToFock a
     cont := finiteParticleCoreToFock_continuous a } : FiniteParticleCore →L[ℂ] FockHilbert a).comp
    (coreCreationSmearCLM v)

@[simp] theorem fockCreationSmearCLM_apply (a : Parameters) (v : FiniteParticleCore)
    (f : 𝓢(Momentum,ℂ)) :
    fockCreationSmearCLM a v f = finiteParticleCoreToFock a (creationCore f v) := rfl

end AASCKleinGordon
