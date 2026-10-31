import KGEnergyTemperate
import KGFockCoreSpatialCharges

noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem particleTotalEnergyComplex_temperate (a : Parameters) (n : ℕ) :
    (fun x => (particleTotalEnergy a n x : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp (particleTotalEnergy_temperate a n)

def schwartzTotalEnergy (a : Parameters) (n : ℕ) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (particleTotalEnergy a n x : ℂ))

theorem schwartzTotalEnergy_apply (a : Parameters) (n : ℕ)
    (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    schwartzTotalEnergy a n f x=(particleTotalEnergy a n x : ℂ)*f x :=
  SchwartzMap.smulLeftCLM_apply_apply (particleTotalEnergyComplex_temperate a n) f x

def sectorEnergy (a : Parameters) (n : ℕ) : bosonicSchwartz n →ₗ[ℂ] bosonicSchwartz n where
  toFun f := ⟨schwartzTotalEnergy a n f.val,by
    intro σ x
    rw [schwartzTotalEnergy_apply,schwartzTotalEnergy_apply,particleTotalEnergy_permutation,f.property]⟩
  map_add' f g := by apply Subtype.ext; exact (schwartzTotalEnergy a n).map_add f.val g.val
  map_smul' c f := by apply Subtype.ext; exact (schwartzTotalEnergy a n).map_smul c f.val

def coreEnergy (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => sectorEnergy a n)

def fockCoreEnergy (a : Parameters) : FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (coreEnergy a)).comp (fockCoreDomainEquiv a).symm.toLinearMap

theorem fockCoreEnergy_on_original_core (a : Parameters) (f : FiniteParticleCore) :
    fockCoreEnergy a (includedFockCore a f)=finiteParticleCoreToFock a (coreEnergy a f) := by
  change finiteParticleCoreToFock a (coreEnergy a
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a f)))=_
  rw [LinearEquiv.symm_apply_apply]

theorem fockCoreEnergy_domain_dense (a : Parameters) :
    Dense ((fockCoreEnergy a).domain : Set (FockHilbert a)) := finiteParticleCoreToFock_dense a

theorem fockCoreEnergy_preserves_common_domain (a : Parameters) (f : fockCoreDomain a) :
    fockCoreEnergy a f ∈ fockCoreDomain a := ⟨coreEnergy a ((fockCoreDomainEquiv a).symm f),rfl⟩

theorem fockMaximalEnergy_graph_on_original_core (a : Parameters) (f : FiniteParticleCore) :
    (finiteParticleCoreToFock a f,finiteParticleCoreToFock a (coreEnergy a f)) ∈
      (fockMaximalEnergy a).graph := by
  apply (fockRealMultiplication_mem_graph _ _ _ _ _ _).2
  intro n
  simp only [finiteParticleCoreToFock_component]
  have h1 := (schwartzTotalEnergy a n (f n).val).coeFn_toLp 2 (particleMeasure a n)
  have h2 := (f n).val.coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2] with x hx hy
  change ((schwartzTotalEnergy a n (f n).val).toLp 2 (particleMeasure a n)) x=
    (particleTotalEnergy a n x : ℂ)*((f n).val.toLp 2 (particleMeasure a n)) x
  rw [hx,hy,schwartzTotalEnergy_apply]

theorem fockCoreEnergy_le_maximal (a : Parameters) : fockCoreEnergy a ≤ fockMaximalEnergy a := by
  apply LinearPMap.le_of_le_graph
  intro z hz
  obtain ⟨f,rfl⟩ := (LinearPMap.mem_graph_iff' _).mp hz
  let u := (fockCoreDomainEquiv a).symm f
  have hf : f=includedFockCore a u := ((fockCoreDomainEquiv a).apply_symm_apply f).symm
  rw [hf,fockCoreEnergy_on_original_core]
  exact fockMaximalEnergy_graph_on_original_core a u

end AASCKleinGordon
