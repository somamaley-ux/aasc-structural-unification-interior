import KGGeneralLorentzOriginalCore
import KGEventTranslationFieldOperations

noncomputable section
set_option maxHeartbeats 1800000
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem particleLorentzMap_swapDelete (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (i : Fin (n+1)) (x : ParticleConfiguration (n+1)) :
    swapDelete n i (particleLorentzMap a (n+1) L x)=
      particleLorentzMap a n L (swapDelete n i x) := rfl

theorem lorentz_creationSector (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    bosonicLorentzSchwartzCLM a (n+1) L (creationSectorCLM n f H)=
      creationSectorCLM n (lorentzSchwartzCLM a L f) (bosonicLorentzSchwartzCLM a n L H) := by
  apply Subtype.ext
  ext x
  rw [bosonicLorentzSchwartz_apply]
  simp only [creationSectorCLM_apply,SchwartzMap.smul_apply,smul_eq_mul,symmetrizer_insert_apply,
    lorentzSchwartzCLM_apply,bosonicLorentzSchwartz_apply,particleLorentzMap_swapDelete]
  rfl

theorem lorentz_creationCore (a : Parameters) (L : ProperLorentzTransform)
    (f : 𝓢(Momentum,ℂ)) (u : FiniteParticleCore) :
    coreLorentz a L (creationCore f u)=
      creationCore (lorentzSchwartzCLM a L f) (coreLorentz a L u) := by
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
    change coreLorentz a L (creationCore f
      (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))=
        creationCore (lorentzSchwartzCLM a L f)
          (coreLorentz a L (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
    rw [creationCore_lof,coreLorentz_lof,coreLorentz_lof,creationCore_lof,lorentz_creationSector]

end AASCKleinGordon
