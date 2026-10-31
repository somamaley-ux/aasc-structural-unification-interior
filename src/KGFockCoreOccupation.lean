import KGBosonicCoreEmbedding

noncomputable section
open MeasureTheory
open scoped DirectSum SchwartzMap ENNReal
namespace AASCKleinGordon

theorem finiteParticleCoreToFock_component (a : Parameters) (v : FiniteParticleCore) (n : ℕ) :
    finiteParticleCoreToFock a v n=bosonicCoreToSector a n (v n) := by
  classical
  refine DirectSum.induction_on v ?_ ?_ ?_
  · simp
  · intro i f
    change finiteParticleCoreToFock a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) i f) n=_
    rw [finiteParticleCoreToFock_on_sector]
    by_cases h : i=n
    · subst i
      simp
    · simp [lp.single_apply,Pi.single_apply,DirectSum.lof_eq_of,DirectSum.of_apply,h,Ne.symm h]
  · intro x y hx hy
    simp only [map_add,lp.coeFn_add,DFinsupp.add_apply,Pi.add_apply,hx,hy]
    change _ = bosonicCoreToSector a n (x n+y n)
    rw [map_add]

theorem finiteParticleCoreToFock_injective (a : Parameters) :
    Function.Injective (finiteParticleCoreToFock a) := by
  intro v w h
  apply DFinsupp.ext
  intro n
  apply bosonicCoreToSector_injective a n
  simpa only [finiteParticleCoreToFock_component] using
    congrArg (fun f : FockHilbert a => f n) h

def fockVacuum (a : Parameters) : FockHilbert a := finiteParticleCoreToFock a vacuumCore
def fockParticle (a : Parameters) : FockHilbert a := finiteParticleCoreToFock a oneParticleCore

theorem fockVacuum_nonzero (a : Parameters) : fockVacuum a≠0 := by
  intro h
  exact vacuumCore_nonzero (finiteParticleCoreToFock_injective a (h.trans (map_zero _).symm))

theorem fockParticle_nonzero (a : Parameters) : fockParticle a≠0 := by
  intro h
  exact oneParticleCore_nonzero (finiteParticleCoreToFock_injective a (h.trans (map_zero _).symm))

theorem fockVacuum_ne_particle (a : Parameters) : fockVacuum a≠fockParticle a := by
  intro h
  exact vacuum_and_particle_distinct (finiteParticleCoreToFock_injective a h)

instance vacuumParticleMeasure_probability (a : Parameters) : IsProbabilityMeasure (particleMeasure a 0) where
  measure_univ := by simp [particleMeasure,Measure.pi_univ]

theorem fockVacuum_norm (a : Parameters) : ‖fockVacuum a‖=1 := by
  change ‖finiteParticleCoreToFock a
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 0 vacuumSector)‖=1
  rw [finiteParticleCoreToFock_on_sector,lp.norm_single (by norm_num : 0 < (2:ℝ≥0∞))]
  change ‖particleSchwartzToHilbert a 0 vacuumSchwartz‖=1
  rw [Lp.norm_def]
  have he : (particleSchwartzToHilbert a 0 vacuumSchwartz : ParticleConfiguration 0 → ℂ)=ᵐ[particleMeasure a 0]
      (fun _ => (1 : ℂ)) := vacuumSchwartz.coeFn_toLp 2 (particleMeasure a 0)
  rw [eLpNorm_congr_ae he,eLpNorm_const' (1:ℂ) (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠⊤)]
  simp

end AASCKleinGordon
