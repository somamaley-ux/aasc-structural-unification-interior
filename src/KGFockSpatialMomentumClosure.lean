import KGFockMaximalMultiplication
import KGSchwartzMomentumCoefficient
import HilbertBoundedPairCore

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

def coreMomentumCoefficientB (j : Fin 3) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => bosonicSchwartzMomentumCoefficientB n j)

theorem fockMomentumCoefficientB_intertwines_core (a : Parameters) (j : Fin 3)
    (f : FiniteParticleCore) :
    fockCoefficientB a (fun n => totalMomentumCLM n j) (fun n => (totalMomentumCLM n j).measurable)
        (fun n => totalMomentum_particlePermutation n j) (finiteParticleCoreToFock a f)=
      finiteParticleCoreToFock a (coreMomentumCoefficientB j f) := by
  apply lp.ext
  funext n
  change sectorCoefficientB a _ _ _ n (finiteParticleCoreToFock a f n)=
    finiteParticleCoreToFock a (coreMomentumCoefficientB j f) n
  simp only [finiteParticleCoreToFock_component]
  apply Subtype.ext
  change Multiplication.graphBoundedB (totalMomentumCLM n j) (totalMomentumCLM n j).measurable
      (bosonicCoreToSector a n (f n)).val=
    (bosonicCoreToSector a n (bosonicSchwartzMomentumCoefficientB n j (f n))).val
  exact bosonicMomentumCoefficientB_intertwines a n j (f n)

theorem fockMomentumCoefficientB_preserves_core (a : Parameters) (j : Fin 3)
    (f : (fockCoreSpatialCharge a j).domain) :
    fockCoefficientB a (fun n => totalMomentumCLM n j) (fun n => (totalMomentumCLM n j).measurable)
        (fun n => totalMomentum_particlePermutation n j) f.val ∈ (fockCoreSpatialCharge a j).domain := by
  obtain ⟨u,hu⟩ := f.property
  refine ⟨coreMomentumCoefficientB j u,?_⟩
  rw [← hu,fockMomentumCoefficientB_intertwines_core]

theorem fockCoreSpatialCharge_closure_eq_maximal (a : Parameters) (j : Fin 3) :
    (fockCoreSpatialCharge a j).closure=fockMaximalSpatialMomentum a j :=
  BoundedPair.closure_eq_of_dense_invariant_core _ _
    (fockCoefficientB_injective a (fun n => totalMomentumCLM n j)
      (fun n => (totalMomentumCLM n j).measurable) (fun n => totalMomentum_particlePermutation n j))
    (fockCoefficients_commute a (fun n => totalMomentumCLM n j)
      (fun n => (totalMomentumCLM n j).measurable) (fun n => totalMomentum_particlePermutation n j))
    (fockCoefficients_normalized a (fun n => totalMomentumCLM n j)
      (fun n => (totalMomentumCLM n j).measurable) (fun n => totalMomentum_particlePermutation n j))
    (fockCoreSpatialCharge a j) (fockCoreSpatialCharge_domain_dense a j)
    (fockCoreSpatialCharge_le_maximal a j) (fockMomentumCoefficientB_preserves_core a j)

theorem fockCoreSpatialCharge_closure_selfAdjoint (a : Parameters) (j : Fin 3) :
    IsSelfAdjoint (fockCoreSpatialCharge a j).closure := by
  rw [fockCoreSpatialCharge_closure_eq_maximal]
  exact fockMaximalSpatialMomentum_selfAdjoint a j

end AASCKleinGordon
