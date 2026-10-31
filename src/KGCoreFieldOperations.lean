import KGSchwartzContraction
import KGFiniteParticleTopology
import KGFockCoreSpatialCharges

noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

def creationCore (f : 𝓢(Momentum,ℂ)) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.toModule ℂ ℕ FiniteParticleCore fun n =>
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) (n+1)).comp
      (creationSectorCLM n f).toLinearMap

def annihilationOnSector (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    (n : ℕ) → bosonicSchwartz n →ₗ[ℂ] FiniteParticleCore
  | 0 => 0
  | n+1 => (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n).comp
      (annihilationSectorCLM a n f).toLinearMap

def annihilationCore (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.toModule ℂ ℕ FiniteParticleCore (annihilationOnSector a f)

@[simp] theorem creationCore_lof (f : 𝓢(Momentum,ℂ)) (n : ℕ) (H : bosonicSchwartz n) :
    creationCore f (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H) =
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) (n+1) (creationSectorCLM n f H) := by
  simp [creationCore]

@[simp] theorem annihilationCore_lof_zero (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz 0) :
    annihilationCore a f (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 0 H) = 0 := by
  simp [annihilationCore, annihilationOnSector]

@[simp] theorem annihilationCore_lof_succ (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (n : ℕ) (H : bosonicSchwartz (n+1)) :
    annihilationCore a f (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) (n+1) H) =
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (annihilationSectorCLM a n f H) := by
  simp [annihilationCore, annihilationOnSector]

theorem creationCore_continuous (f : 𝓢(Momentum,ℂ)) : Continuous (creationCore f) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  change Continuous (fun H : bosonicSchwartz n => creationCore f
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp_rw [creationCore_lof]
  exact (finiteParticleCore_lof_continuous (n+1)).comp (creationSectorCLM n f).continuous

theorem annihilationCore_continuous (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    Continuous (annihilationCore a f) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  cases n with
  | zero =>
      change Continuous (fun H : bosonicSchwartz 0 => annihilationCore a f
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 0 H))
      simp_rw [annihilationCore_lof_zero]
      exact continuous_const
  | succ n =>
      change Continuous (fun H : bosonicSchwartz (n+1) => annihilationCore a f
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) (n+1) H))
      simp_rw [annihilationCore_lof_succ]
      exact (finiteParticleCore_lof_continuous n).comp (annihilationSectorCLM a n f).continuous

theorem annihilationCore_vacuum_zero (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    annihilationCore a f vacuumCore = 0 := by
  exact annihilationCore_lof_zero a f vacuumSector

def fockCoreCreation (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (creationCore f)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

def fockCoreAnnihilation (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (annihilationCore a f)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

theorem fockCoreCreation_on_original_core (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (v : FiniteParticleCore) :
    fockCoreCreation a f (includedFockCore a v) = finiteParticleCoreToFock a (creationCore f v) := by
  change finiteParticleCoreToFock a (creationCore f
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a v))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fockCoreAnnihilation_on_original_core (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (v : FiniteParticleCore) :
    fockCoreAnnihilation a f (includedFockCore a v) = finiteParticleCoreToFock a (annihilationCore a f v) := by
  change finiteParticleCoreToFock a (annihilationCore a f
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a v))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fockCoreCreation_preserves_original_core (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (v : fockCoreDomain a) : fockCoreCreation a f v ∈ fockCoreDomain a :=
  ⟨creationCore f ((fockCoreDomainEquiv a).symm v), rfl⟩

theorem fockCoreAnnihilation_preserves_original_core (a : Parameters) (f : 𝓢(Momentum,ℂ))
    (v : fockCoreDomain a) : fockCoreAnnihilation a f v ∈ fockCoreDomain a :=
  ⟨annihilationCore a f ((fockCoreDomainEquiv a).symm v), rfl⟩

end AASCKleinGordon
