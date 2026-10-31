import KGOneParticleHilbert

/-! Exact coordinate transport between the n=1 finite-particle core and the
weighted one-particle Hilbert space. No implicit identification of the
configuration types or assumed dense embedding is used. -/
noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

def oneConfigurationEquiv : ParticleConfiguration 1 ≃L[ℝ] Momentum :=
  ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => Momentum)

def sectorOneToSchwartz : bosonicSchwartz 1 →L[ℂ] 𝓢(Momentum,ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ oneConfigurationEquiv.symm).comp
    (bosonicSchwartz 1).subtypeL

theorem sectorOneToSchwartz_apply (f : bosonicSchwartz 1) (p : Momentum) :
    sectorOneToSchwartz f p=f.val (oneConfigurationEquiv.symm p) := rfl

def sectorOneOfSchwartz (f : 𝓢(Momentum,ℂ)) : bosonicSchwartz 1 :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ oneConfigurationEquiv f,by
    intro σ x
    have hx : (fun i => x (σ i))=x :=
      funext (fun i => congrArg x (Subsingleton.elim (σ i) i))
    rw [hx]⟩

theorem sectorOneToSchwartz_surjective : Function.Surjective sectorOneToSchwartz := by
  intro f
  refine ⟨sectorOneOfSchwartz f,?_⟩
  ext p
  change f (oneConfigurationEquiv (oneConfigurationEquiv.symm p))=f p
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem sectorOneToSchwartz_injective : Function.Injective sectorOneToSchwartz := by
  intro f g h
  apply Subtype.ext
  ext x
  have he := congrArg (fun v : 𝓢(Momentum,ℂ) => v (oneConfigurationEquiv x)) h
  simpa [sectorOneToSchwartz_apply] using he

def oneParticleSectorToHilbert (a : Parameters) : bosonicSchwartz 1 →L[ℂ] OneParticleHilbert a :=
  (oneParticleSchwartzToHilbert a).comp sectorOneToSchwartz

theorem oneParticleSectorToHilbert_injective (a : Parameters) :
    Function.Injective (oneParticleSectorToHilbert a) :=
  (oneParticleSchwartz_injective a).comp sectorOneToSchwartz_injective

theorem oneParticleSectorToHilbert_dense (a : Parameters) :
    DenseRange (oneParticleSectorToHilbert a) := by
  intro y
  apply closure_mono (s:=Set.range (oneParticleSchwartzToHilbert a)) ?_ (oneParticleSchwartz_dense a y)
  rintro z ⟨f,rfl⟩
  obtain ⟨g,hg⟩ := sectorOneToSchwartz_surjective f
  exact ⟨g,by simp [oneParticleSectorToHilbert,ContinuousLinearMap.comp_apply,hg]⟩

theorem embedded_one_particle_nonzero (a : Parameters) :
    oneParticleSectorToHilbert a oneParticleSector≠0 := by
  intro h
  have hz : oneParticleSector=(0 : bosonicSchwartz 1) :=
    oneParticleSectorToHilbert_injective a (h.trans (map_zero _).symm)
  have he := congrArg (fun f : bosonicSchwartz 1 => f.val 0) hz
  simpa [oneParticleSector,oneParticleSchwartz_at_zero] using he

end AASCKleinGordon
