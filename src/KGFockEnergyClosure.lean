import KGSchwartzEnergyCoefficient
import HilbertBoundedPairCore

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

def coreEnergyCoefficientB (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => bosonicSchwartzEnergyCoefficientB a n)

theorem fockEnergyCoefficientB_intertwines_core (a : Parameters) (f : FiniteParticleCore) :
    fockCoefficientB a (particleTotalEnergy a) (fun n => (particleTotalEnergy_continuous a n).measurable)
        (particleTotalEnergy_particlePermutation a) (finiteParticleCoreToFock a f)=
      finiteParticleCoreToFock a (coreEnergyCoefficientB a f) := by
  apply lp.ext
  funext n
  change sectorCoefficientB a _ _ _ n (finiteParticleCoreToFock a f n)=
    finiteParticleCoreToFock a (coreEnergyCoefficientB a f) n
  simp only [finiteParticleCoreToFock_component]
  apply Subtype.ext
  change Multiplication.graphBoundedB (particleTotalEnergy a n) (particleTotalEnergy_continuous a n).measurable
      (bosonicCoreToSector a n (f n)).val=
    (bosonicCoreToSector a n (bosonicSchwartzEnergyCoefficientB a n (f n))).val
  exact bosonicEnergyCoefficientB_intertwines a n (f n)

theorem fockEnergyCoefficientB_preserves_core (a : Parameters) (f : (fockCoreEnergy a).domain) :
    fockCoefficientB a (particleTotalEnergy a) (fun n => (particleTotalEnergy_continuous a n).measurable)
        (particleTotalEnergy_particlePermutation a) f.val ∈ (fockCoreEnergy a).domain := by
  obtain ⟨u,hu⟩ := f.property
  refine ⟨coreEnergyCoefficientB a u,?_⟩
  rw [← hu,fockEnergyCoefficientB_intertwines_core]

theorem fockCoreEnergy_closure_eq_maximal (a : Parameters) :
    (fockCoreEnergy a).closure=fockMaximalEnergy a :=
  BoundedPair.closure_eq_of_dense_invariant_core _ _
    (fockCoefficientB_injective a (particleTotalEnergy a)
      (fun n => (particleTotalEnergy_continuous a n).measurable) (particleTotalEnergy_particlePermutation a))
    (fockCoefficients_commute a (particleTotalEnergy a)
      (fun n => (particleTotalEnergy_continuous a n).measurable) (particleTotalEnergy_particlePermutation a))
    (fockCoefficients_normalized a (particleTotalEnergy a)
      (fun n => (particleTotalEnergy_continuous a n).measurable) (particleTotalEnergy_particlePermutation a))
    (fockCoreEnergy a) (fockCoreEnergy_domain_dense a) (fockCoreEnergy_le_maximal a)
    (fockEnergyCoefficientB_preserves_core a)

theorem fockCoreEnergy_closure_selfAdjoint (a : Parameters) :
    IsSelfAdjoint (fockCoreEnergy a).closure := by
  rw [fockCoreEnergy_closure_eq_maximal]
  exact fockMaximalEnergy_selfAdjoint a

end AASCKleinGordon
