import KGWeylCoherentCoreGenerator

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem tensorPower_lorentz (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (f : 𝓢(Momentum,ℂ)) :
    bosonicLorentzSchwartzCLM a n L (bosonicTensorPower f n)=
      bosonicTensorPower (lorentzSchwartzCLM a L f) n := by
  apply Subtype.ext
  ext x
  simp only [bosonicLorentzSchwartz_apply,bosonicTensorPower,schwartzTensorPower_apply,
    lorentzSchwartzCLM_apply]
  rfl

theorem fockLorentz_exponentialVector (a : Parameters) (L : ProperLorentzTransform)
    (f : 𝓢(Momentum,ℂ)) :
    fockLorentzUnitary a L (exponentialVector a f)=
      exponentialVector a (lorentzSchwartzCLM a L f) := by
  apply lp.ext
  funext n
  change bosonicLorentzUnitary a n L (coherentSector a f n)=
    coherentSector a (lorentzSchwartzCLM a L f) n
  simp only [coherentSector,bosonicTensorPowerHilbert,map_smul,
    bosonicLorentz_intertwines_original_schwartz,tensorPower_lorentz]

theorem particleEventTranslationPhase_product (a : Parameters) (n : ℕ)
    (b : Spacetime) (x : ParticleConfiguration n) :
    particleEventTranslationPhase a n b x=∏i,eventTranslationPhase a b (x i) := by
  classical
  have hh : ∀ S : Finset (Fin n),
      Translation.phase a.hbar 1 (∑i∈S,eventMomentumPair a b (x i))=
        ∏i∈S,eventTranslationPhase a b (x i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [Translation.phase]
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi,Finset.prod_insert hi,translationPhase_add_value,ih]
      rfl
  exact hh Finset.univ

theorem tensorPower_eventTranslation (a : Parameters) (n : ℕ) (b : Spacetime)
    (f : 𝓢(Momentum,ℂ)) :
    bosonicEventTranslationSchwartzCLM a n b (bosonicTensorPower f n)=
      bosonicTensorPower (eventTranslationSchwartzCLM a b f) n := by
  apply Subtype.ext
  ext x
  simp only [bosonicEventTranslationSchwartz_apply,bosonicTensorPower,
    schwartzTensorPower_apply,eventTranslationSchwartz_apply,
    particleEventTranslationPhase_product,Finset.prod_mul_distrib]

theorem fockEventTranslation_exponentialVector (a : Parameters) (b : Spacetime)
    (f : 𝓢(Momentum,ℂ)) :
    fockEventTranslation a b (exponentialVector a f)=
      exponentialVector a (eventTranslationSchwartzCLM a b f) := by
  apply lp.ext
  funext n
  change bosonicPhaseMultiplier a n (particleEventMomentum a n b)
    (particleEventMomentum_continuous a n b).measurable
    (particleEventMomentum_permutation a n b) a.hbar 1 (coherentSector a f n)=
      coherentSector a (eventTranslationSchwartzCLM a b f) n
  simp only [coherentSector,bosonicTensorPowerHilbert,map_smul,
    bosonicEventTranslation_intertwines_original_schwartz,tensorPower_eventTranslation]

def poincareSchwartzCLM (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  (eventTranslationSchwartzCLM a b).comp (lorentzSchwartzCLM a L)

theorem fockPoincare_exponentialVector (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (f : 𝓢(Momentum,ℂ)) :
    fockPoincareUnitary a b L (exponentialVector a f)=
      exponentialVector a (poincareSchwartzCLM a b L f) := by
  change fockEventTranslation a b (fockLorentzUnitary a L (exponentialVector a f))=_
  rw [fockLorentz_exponentialVector,fockEventTranslation_exponentialVector]
  rfl

end AASCKleinGordon
