import KGRealSpacetimeLift
import KGWeylOneParticleLimits

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

/-- Exactly the real condition of the original global spacetime field. -/
def realSpacetimeTestSpace : Submodule ℝ 𝓢(Spacetime,ℂ) :=
  (conjugateSchwartzCLM-ContinuousLinearMap.id ℝ 𝓢(Spacetime,ℂ)).ker

theorem mem_realSpacetimeTestSpace (h : 𝓢(Spacetime,ℂ)) :
    h∈realSpacetimeTestSpace ↔ conjugateSchwartzCLM h=h := by
  change conjugateSchwartzCLM h-h=0 ↔ _
  exact sub_eq_zero

def originalRealSmearingCLM (a : Parameters) :
    realSpacetimeTestSpace →L[ℝ] 𝓢(Momentum,ℂ) :=
  ((spacetimeSmearingCLM a).restrictScalars ℝ).comp realSpacetimeTestSpace.subtypeL

def originalRealSpacetimeLift (a : Parameters) (f : 𝓢(Momentum,ℂ)) : realSpacetimeTestSpace :=
  ⟨realSpacetimeLiftCLM a f,(mem_realSpacetimeTestSpace _).mpr (realSpacetimeLift_real a f)⟩

theorem originalRealSmearing_right_inverse (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    originalRealSmearingCLM a (originalRealSpacetimeLift a f)=f :=
  realSpacetimeLift_smearing a f

theorem originalRealSmearing_surjective (a : Parameters) :
    Function.Surjective (originalRealSmearingCLM a) :=
  fun f => ⟨originalRealSpacetimeLift a f,originalRealSmearing_right_inverse a f⟩

theorem originalRealSmearing_oneParticle_dense (a : Parameters) :
    DenseRange (fun h : realSpacetimeTestSpace =>
      oneParticleSchwartzToHilbert a (originalRealSmearingCLM a h)) := by
  have hr : Set.range (fun h : realSpacetimeTestSpace =>
      oneParticleSchwartzToHilbert a (originalRealSmearingCLM a h))=
      Set.range (oneParticleSchwartzToHilbert a) := by
    ext v
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨originalRealSmearingCLM a h,rfl⟩
    · rintro ⟨f,rfl⟩
      exact ⟨originalRealSpacetimeLift a f,congrArg (oneParticleSchwartzToHilbert a)
        (originalRealSmearing_right_inverse a f)⟩
  simpa only [DenseRange,hr] using oneParticleSchwartz_dense a

/-- Imaginary displacement label with the exact original Segal-field amplitude.
The corresponding real-time orbit differentiates with sign +i times that field. -/
def realFieldWeylLabelCLM (a : Parameters) (s : ℝ) :
    realSpacetimeTestSpace →L[ℝ] 𝓢(Momentum,ℂ) :=
  (Complex.I*(s : ℂ)) • originalRealSmearingCLM a

theorem realFieldWeylLabel_surjective (a : Parameters) (s : ℝ) (hs : s≠0) :
    Function.Surjective (realFieldWeylLabelCLM a s) := by
  intro g
  let c : ℂ:=Complex.I*(s : ℂ)
  have hc : c≠0:=mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hs)
  refine ⟨originalRealSpacetimeLift a (c⁻¹ • g),?_⟩
  change c • originalRealSmearingCLM a (originalRealSpacetimeLift a (c⁻¹ • g))=g
  rw [originalRealSmearing_right_inverse,smul_smul,mul_inv_cancel₀ hc,one_smul]

theorem realFieldWeylLabel_zero_amplitude (a : Parameters) (h : realSpacetimeTestSpace) :
    realFieldWeylLabelCLM a 0 h=0 := by
  simp [realFieldWeylLabelCLM]

end AASCKleinGordon
