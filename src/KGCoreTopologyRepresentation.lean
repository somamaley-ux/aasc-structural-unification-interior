import KGCoreFieldOperations
import KGCoreEnergy

noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem finiteParticleCoreToFock_continuous (a : Parameters) :
    Continuous (finiteParticleCoreToFock a) := by
  apply (core_normed_linearMap_continuous_iff _).mpr
  intro n
  change Continuous (fun H : bosonicSchwartz n => finiteParticleCoreToFock a
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp_rw [finiteParticleCoreToFock_on_sector]
  exact (lp.singleContinuousLinearMap ℂ (fun k : ℕ => bosonicHilbertSector a k) 2 n).continuous.comp
    (bosonicCoreToSector a n).continuous

theorem coreEnergy_continuous (a : Parameters) : Continuous (coreEnergy a) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  have hsector : Continuous (sectorEnergy a n) := by
    change Continuous (fun H : bosonicSchwartz n =>
      (⟨schwartzTotalEnergy a n H.val, _⟩ : bosonicSchwartz n))
    exact ((schwartzTotalEnergy a n).continuous.comp continuous_subtype_val).subtype_mk _
  change Continuous (fun H : bosonicSchwartz n => coreEnergy a
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp only [coreEnergy, DirectSum.lmap_lof]
  exact (finiteParticleCore_lof_continuous n).comp hsector

theorem coreSpatialMomentum_continuous (j : Fin 3) : Continuous (coreSpatialMomentum j) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  have hsector : Continuous (sectorSpatialMomentum n j) := by
    change Continuous (fun H : bosonicSchwartz n =>
      (⟨schwartzTotalMomentum n j H.val, _⟩ : bosonicSchwartz n))
    exact ((schwartzTotalMomentum n j).continuous.comp continuous_subtype_val).subtype_mk _
  change Continuous (fun H : bosonicSchwartz n => coreSpatialMomentum j
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp_rw [coreSpatialMomentum_on_sector]
  exact (finiteParticleCore_lof_continuous n).comp hsector

theorem original_energy_graphMap_continuous (a : Parameters) :
    Continuous (fun v : FiniteParticleCore =>
      (finiteParticleCoreToFock a v, fockCoreEnergy a (includedFockCore a v))) := by
  simp_rw [fockCoreEnergy_on_original_core]
  exact (finiteParticleCoreToFock_continuous a).prodMk
    ((finiteParticleCoreToFock_continuous a).comp (coreEnergy_continuous a))

theorem original_spatial_graphMap_continuous (a : Parameters) (j : Fin 3) :
    Continuous (fun v : FiniteParticleCore =>
      (finiteParticleCoreToFock a v, fockCoreSpatialCharge a j (includedFockCore a v))) := by
  simp_rw [fockCoreSpatialCharge_on_original_core]
  exact (finiteParticleCoreToFock_continuous a).prodMk
    ((finiteParticleCoreToFock_continuous a).comp (coreSpatialMomentum_continuous j))

theorem original_creation_graphMap_continuous (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    Continuous (fun v : FiniteParticleCore =>
      (finiteParticleCoreToFock a v, fockCoreCreation a f (includedFockCore a v))) := by
  simp_rw [fockCoreCreation_on_original_core]
  exact (finiteParticleCoreToFock_continuous a).prodMk
    ((finiteParticleCoreToFock_continuous a).comp (creationCore_continuous f))

theorem original_annihilation_graphMap_continuous (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    Continuous (fun v : FiniteParticleCore =>
      (finiteParticleCoreToFock a v, fockCoreAnnihilation a f (includedFockCore a v))) := by
  simp_rw [fockCoreAnnihilation_on_original_core]
  exact (finiteParticleCoreToFock_continuous a).prodMk
    ((finiteParticleCoreToFock_continuous a).comp (annihilationCore_continuous a f))

end AASCKleinGordon
