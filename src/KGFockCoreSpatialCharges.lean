import KGFockCoreDensity
import KGCoreSpatialMomentum
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Concrete partial spatial charges on the actual dense Fock common core.
No bounded total extension, selfadjoint closure, translation generator or
EMT integral identity is assumed. These further analytic/source identities
must be proved on this same carrier. -/
noncomputable section
namespace AASCKleinGordon

def fockCoreDomain (a : Parameters) : Submodule ℂ (FockHilbert a) :=
  LinearMap.range (finiteParticleCoreToFock a)

def fockCoreDomainEquiv (a : Parameters) : FiniteParticleCore ≃ₗ[ℂ] fockCoreDomain a :=
  LinearEquiv.ofInjective (finiteParticleCoreToFock a) (finiteParticleCoreToFock_injective a)

def fockCoreSpatialCharge (a : Parameters) (j : Fin 3) : FockHilbert a →ₗ.[ℂ] FockHilbert a where
  domain := fockCoreDomain a
  toFun := ((finiteParticleCoreToFock a).comp (coreSpatialMomentum j)).comp
    (fockCoreDomainEquiv a).symm.toLinearMap

def includedFockCore (a : Parameters) (v : FiniteParticleCore) : fockCoreDomain a :=
  fockCoreDomainEquiv a v

theorem includedFockCore_val (a : Parameters) (v : FiniteParticleCore) :
    (includedFockCore a v).val=finiteParticleCoreToFock a v := rfl

theorem fockCoreSpatialCharge_on_original_core (a : Parameters) (j : Fin 3) (v : FiniteParticleCore) :
    fockCoreSpatialCharge a j (includedFockCore a v)=finiteParticleCoreToFock a (coreSpatialMomentum j v) := by
  change finiteParticleCoreToFock a (coreSpatialMomentum j
    ((fockCoreDomainEquiv a).symm (fockCoreDomainEquiv a v)))=_
  rw [LinearEquiv.symm_apply_apply]

theorem fockCoreSpatialCharge_domain_dense (a : Parameters) (j : Fin 3) :
    Dense ((fockCoreSpatialCharge a j).domain : Set (FockHilbert a)) := finiteParticleCoreToFock_dense a

theorem fockCoreSpatialCharge_preserves_common_domain (a : Parameters) (j : Fin 3)
    (v : fockCoreDomain a) : fockCoreSpatialCharge a j v ∈ fockCoreDomain a := by
  exact ⟨coreSpatialMomentum j ((fockCoreDomainEquiv a).symm v),rfl⟩

theorem fockCoreSpatialCharges_commute_on_original_core (a : Parameters) (i j : Fin 3)
    (v : FiniteParticleCore) :
    fockCoreSpatialCharge a i (includedFockCore a (coreSpatialMomentum j v))=
      fockCoreSpatialCharge a j (includedFockCore a (coreSpatialMomentum i v)) := by
  rw [fockCoreSpatialCharge_on_original_core,fockCoreSpatialCharge_on_original_core]
  apply congrArg (finiteParticleCoreToFock a)
  exact congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L v)
    (core_spatial_momenta_commute i j)

theorem fockCoreSpatialCharge_vacuum_zero (a : Parameters) (j : Fin 3) :
    fockCoreSpatialCharge a j (includedFockCore a vacuumCore)=0 := by
  rw [fockCoreSpatialCharge_on_original_core,coreSpatialMomentum_vacuum_zero,map_zero]

end AASCKleinGordon
