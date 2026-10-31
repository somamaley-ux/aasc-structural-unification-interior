import KGCoherentFactorialNormalization
import KGBosonicAdjointness

noncomputable section
set_option maxHeartbeats 2600000
open scoped SchwartzMap
namespace AASCKleinGordon

def coherentSectorCore (f : 𝓢(Momentum,ℂ)) (n : ℕ) : bosonicSchwartz n :=
  coherentFactor n • bosonicTensorPower f n

theorem coherentSectorCore_embedding (a : Parameters) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    bosonicCoreToSector a n (coherentSectorCore f n)=coherentSector a f n := by
  rw [coherentSectorCore,map_smul]
  rfl

theorem annihilation_coherentSectorCore (a : Parameters) (f g : 𝓢(Momentum,ℂ)) (n : ℕ) :
    annihilationSectorCLM a n g (coherentSectorCore f (n+1))=
      inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) •
        coherentSectorCore f n := by
  apply Subtype.ext
  rw [coherentSectorCore,map_smul]
  change coherentFactor (n+1) •
    ((Real.sqrt (n+1) : ℂ) • particleContractionCLM a n g (schwartzTensorPower f (n+1)))=_
  rw [schwartzTensorPower,particleContraction_tensorInsert,test_pair_integral_eq_inner]
  change coherentFactor (n+1) • ((Real.sqrt (n+1) : ℂ) •
      (inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) • schwartzTensorPower f n))=
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) •
      (coherentFactor n • schwartzTensorPower f n)
  simp only [smul_smul]
  congr 1
  calc
    _=inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f)*
      ((Real.sqrt (n+1 : ℝ) : ℂ)*coherentFactor (n+1)) := by ring
    _=_ := by rw [coherentFactor_succ]

end AASCKleinGordon
