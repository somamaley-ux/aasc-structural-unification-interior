import WickCovariantUnitary
import WickIsolatedMassSector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

def wickOneConfigurationME : ParticleConfiguration 1 ≃ᵐ Momentum :=
  MeasurableEquiv.piUnique (fun _ : Fin 1 => Momentum)

theorem wick_one_configuration_measure (a : Parameters) :
    MeasurePreserving wickOneConfigurationME (particleMeasure a 1) (wignerMeasure a) :=
  measurePreserving_piUnique (fun _ : Fin 1 => wignerMeasure a)

def wickOneConfigurationUnitary (a : Parameters) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] ParticleHilbert a 1 :=
  lpMeasureEquivalence wickOneConfigurationME (wick_one_configuration_measure a)
    (MeasurePreserving.symm wickOneConfigurationME (wick_one_configuration_measure a))

theorem wick_one_configuration_unitary_ae (a : Parameters) (f : OneParticleHilbert a) :
    wickOneConfigurationUnitary a f =ᵐ[particleMeasure a 1] (fun x => f (x 0)) :=
  Lp.coeFn_compMeasurePreserving f (wick_one_configuration_measure a)

theorem wick_one_particle_permutation (σ : Equiv.Perm (Fin 1)) (x : ParticleConfiguration 1) :
    particlePermutation 1 σ x=x := by
  funext i
  rw [particlePermutation_apply]
  exact congrArg x (Subsingleton.elim _ _)

theorem wick_bosonic_one_all (a : Parameters) (f : ParticleHilbert a 1) :
    f∈bosonicHilbertSector a 1 := by
  apply (bosonicHilbertSector_mem a 1 f).mpr
  intro σ
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (particlePermutation_preserves_measure a 1 σ)] with x hx
  simpa only [wick_one_particle_permutation,Function.comp_apply] using hx

def wickBosonicOneEquiv (a : Parameters) :
    ParticleHilbert a 1 ≃ₗᵢ[ℂ] bosonicHilbertSector a 1 where
  toFun f := ⟨f,wick_bosonic_one_all a f⟩
  invFun f := f.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

def wickOneSectorCoordinates (a : Parameters) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] bosonicHilbertSector a 1 :=
  (wickOneConfigurationUnitary a).trans (wickBosonicOneEquiv a)

theorem wick_one_sector_coordinates_ae (a : Parameters) (f : OneParticleHilbert a) :
    (wickOneSectorCoordinates a f).val =ᵐ[particleMeasure a 1] (fun x => f (x 0)) :=
  wick_one_configuration_unitary_ae a f

theorem wick_one_sector_coordinates_original_core (a : Parameters) (f : bosonicSchwartz 1) :
    wickOneSectorCoordinates a (oneParticleSectorToHilbert a f)=bosonicCoreToSector a 1 f := by
  apply Subtype.ext
  apply Lp.ext
  have h1 := wick_one_sector_coordinates_ae a (oneParticleSectorToHilbert a f)
  have h2 := (wick_one_configuration_measure a).quasiMeasurePreserving.ae
    ((sectorOneToSchwartz f).coeFn_toLp 2 (wignerMeasure a))
  have h3 := f.val.coeFn_toLp 2 (particleMeasure a 1)
  filter_upwards [h1,h2,h3] with x hx hy hz
  change (wickOneSectorCoordinates a (oneParticleSectorToHilbert a f)).val x=
    (f.val.toLp 2 (particleMeasure a 1)) x
  rw [hx,hz]
  change ((sectorOneToSchwartz f).toLp 2 (wignerMeasure a)) (x 0)=f.val x
  rw [show ((sectorOneToSchwartz f).toLp 2 (wignerMeasure a)) (x 0)=sectorOneToSchwartz f (x 0) from hy]
  rw [sectorOneToSchwartz_apply]
  congr 1
  exact oneConfigurationEquiv.symm_apply_apply x

end AASCKleinGordon
