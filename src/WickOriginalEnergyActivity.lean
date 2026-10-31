import KGCoreEnergy
import KGFockExactGenerators
import WickChargeMeasureCoefficient

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped DirectSum
namespace AASCKleinGordon

theorem wick_original_core_energy_component (a : Parameters) (v : FiniteParticleCore)
    (n : ℕ) (x : ParticleConfiguration n) :
    ((coreEnergy a v n).val) x=(particleTotalEnergy a n x : ℂ)*(v n).val x := by
  change schwartzTotalEnergy a n (v n).val x=_
  exact schwartzTotalEnergy_apply a n (v n).val x

theorem wick_original_energy_one_particle_nonzero (a : Parameters) :
    coreEnergy a oneParticleCore≠0 := by
  intro hz
  have evaluated := congrArg (fun v : FiniteParticleCore => (v 1).val 0) hz
  dsimp only at evaluated
  rw [wick_original_core_energy_component] at evaluated
  have one : (oneParticleCore 1).val 0=1 := by
    simp [oneParticleCore,DirectSum.lof_eq_of,DirectSum.of_apply,
      oneParticleSector,oneParticleSchwartz_at_zero]
  rw [one,mul_one] at evaluated
  have positive : 0<particleTotalEnergy a 1 0 := by
    simpa [particleTotalEnergy] using energy_pos a (0 : Momentum)
  exact (Complex.ofReal_ne_zero.mpr positive.ne') evaluated

theorem wick_original_fock_energy_one_particle_nonzero (a : Parameters) :
    finiteParticleCoreToFock a (coreEnergy a oneParticleCore)≠0 := by
  intro hz
  have : coreEnergy a oneParticleCore=0 :=
    (finiteParticleCoreToFock_injective a) (by simpa using hz)
  exact wick_original_energy_one_particle_nonzero a this

/-- Generator normalization is detected on the actual original one-particle
core, not inferred from a vacuum-zero matrix element. -/
theorem wick_original_fock_energy_scale_equality_iff (a : Parameters) (z : ℂ) :
    (∀ v : FiniteParticleCore,z • finiteParticleCoreToFock a (coreEnergy a v)=
      finiteParticleCoreToFock a (coreEnergy a v)) ↔ z=1 := by
  constructor
  · intro same
    have hz : (z-1) • finiteParticleCoreToFock a (coreEnergy a oneParticleCore)=0 := by
      rw [sub_smul,one_smul,same,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right
      (wick_original_fock_energy_one_particle_nonzero a))
  · rintro rfl
    intro v
    exact one_smul _ _

theorem wick_original_core_energy_vacuum_zero (a : Parameters) : coreEnergy a vacuumCore=0 := by
  unfold coreEnergy vacuumCore
  rw [DirectSum.lmap_lof]
  have zero : sectorEnergy a 0 vacuumSector=0 := by
    apply Subtype.ext
    ext x
    change schwartzTotalEnergy a 0 vacuumSector.val x=0
    rw [schwartzTotalEnergy_apply]
    simp [particleTotalEnergy]
  rw [zero,map_zero]

end AASCKleinGordon
