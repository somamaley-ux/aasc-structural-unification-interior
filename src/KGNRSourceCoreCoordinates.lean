import KGSpatialStandingTransport

/-! Exact coordinates of the original core intersection, without a density or
completion argument. The admitted core is unchanged. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
attribute [local irreducible] wickWignerToIsolated kgIsolatedMomentumUnitary
  kgWeightedMomentumUnitary kgOriginalSpatialCoreEquiv kgIsolatedSpatialUnitary
  kgPhysicalSpatialUnitary

def kgOriginalOneCoreOfSchwartz (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    kgOriginalOneCore a :=
  ⟨includedFockCore a (wickOneParticleCore (wickSectorOneOfSchwartzCLM f)),
    wick_isolated_one_particle_contains_original_core a (wickSectorOneOfSchwartzCLM f)⟩

def kgOriginalOneCoreCoordinates (a : Parameters) (x : kgOriginalOneCore a) :
    𝓢(Momentum,ℂ) := sectorOneToSchwartz (((fockCoreDomainEquiv a).symm x.val) 1)

theorem kg_original_one_core_of_schwartz_isolated (a : Parameters)
    (f : 𝓢(Momentum,ℂ)) :
    kgOriginalOneCoreToIsolated a (kgOriginalOneCoreOfSchwartz a f) =
      wickWignerToIsolated a (oneParticleSchwartzToHilbert a f) := by
  change wickOriginalIsolatedCore a (wickSectorOneOfSchwartzCLM f) = _
  calc
    _ = wickWignerToIsolated a
        (oneParticleSectorToHilbert a (wickSectorOneOfSchwartzCLM f)) :=
      (wick_wigner_isolated_original_core a (wickSectorOneOfSchwartzCLM f)).symm
    _ = _ := congrArg (wickWignerToIsolated a)
      (congrArg (oneParticleSchwartzToHilbert a) (wick_sector_one_roundtrip f))

theorem kg_original_one_core_coordinate_reconstruction (a : Parameters)
    (x : kgOriginalOneCore a) :
    kgOriginalOneCoreOfSchwartz a (kgOriginalOneCoreCoordinates a x) = x := by
  have hs : wickSectorOneOfSchwartzCLM (kgOriginalOneCoreCoordinates a x) =
      ((fockCoreDomainEquiv a).symm x.val) 1 := by
    apply sectorOneToSchwartz_injective
    exact wick_sector_one_roundtrip _
  apply Subtype.ext
  apply Subtype.ext
  change finiteParticleCoreToFock a
    (wickOneParticleCore (wickSectorOneOfSchwartzCLM (kgOriginalOneCoreCoordinates a x))) = _
  rw [hs]
  change finiteParticleCoreToFock a
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1
      (((fockCoreDomainEquiv a).symm x.val) 1)) = _
  rw [finiteParticleCoreToFock_on_sector]
  have hcomponent : bosonicCoreToSector a 1 (((fockCoreDomainEquiv a).symm x.val) 1) =
      x.val.val 1 := by
    rw [← finiteParticleCoreToFock_component]
    exact congrArg (fun y : fockCoreDomain a => y.val 1)
      ((fockCoreDomainEquiv a).apply_symm_apply x.val)
  rw [hcomponent]
  exact wick_isolated_reconstruct a (kgOriginalOneCoreToIsolated a x)

theorem kg_original_one_core_coordinates_of_schwartz (a : Parameters)
    (f : 𝓢(Momentum,ℂ)) :
    kgOriginalOneCoreCoordinates a (kgOriginalOneCoreOfSchwartz a f) = f := by
  change sectorOneToSchwartz
    (((fockCoreDomainEquiv a).symm
      (fockCoreDomainEquiv a (wickOneParticleCore (wickSectorOneOfSchwartzCLM f)))) 1) = f
  rw [LinearEquiv.symm_apply_apply]
  change sectorOneToSchwartz ((wickOneCoreCLM (wickSectorOneOfSchwartzCLM f)) 1) = f
  rw [wick_one_core_component_one,wick_sector_one_roundtrip]

theorem kg_original_one_core_coordinates_injective (a : Parameters) :
    Function.Injective (kgOriginalOneCoreCoordinates a) := by
  intro x y h
  rw [← kg_original_one_core_coordinate_reconstruction a x,
    ← kg_original_one_core_coordinate_reconstruction a y,h]

def kgOriginalOneCoreSchwartzEquiv (a : Parameters) :
    𝓢(Momentum,ℂ) ≃ₗ[ℂ] kgOriginalOneCore a where
  toFun := kgOriginalOneCoreOfSchwartz a
  invFun := kgOriginalOneCoreCoordinates a
  left_inv := kg_original_one_core_coordinates_of_schwartz a
  right_inv := kg_original_one_core_coordinate_reconstruction a
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    change finiteParticleCoreToFock a
      (wickOneParticleCore (wickSectorOneOfSchwartzCLM (f+g))) =
      finiteParticleCoreToFock a (wickOneParticleCore (wickSectorOneOfSchwartzCLM f)) +
      finiteParticleCoreToFock a (wickOneParticleCore (wickSectorOneOfSchwartzCLM g))
    simp only [map_add,wickOneParticleCore]
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    change finiteParticleCoreToFock a
      (wickOneParticleCore (wickSectorOneOfSchwartzCLM (c • f))) =
      c • finiteParticleCoreToFock a (wickOneParticleCore (wickSectorOneOfSchwartzCLM f))
    simp only [map_smul,wickOneParticleCore]

theorem kg_original_one_core_momentum_coordinates (a : Parameters)
    (x : kgOriginalOneCore a) :
    kgIsolatedMomentumUnitary a (kgOriginalOneCoreToIsolated a x) =
      kgWeightedMomentumUnitary a
        (oneParticleSchwartzToHilbert a (kgOriginalOneCoreCoordinates a x)) := by
  conv_lhs => rw [← kg_original_one_core_coordinate_reconstruction a x]
  rw [kg_original_one_core_of_schwartz_isolated,
    kg_isolated_momentum_original_normalization]

end AASCKleinGordon
