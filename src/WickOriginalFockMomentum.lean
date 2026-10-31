import WickSectorMomentumExpectation

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

/-- Contravariant physical components on the SAME original algebraic Fock core. -/
def wickOriginalCoreFourMomentum (a : Parameters) (j : Fin 4) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  Fin.cases ((a.speed : ℂ)⁻¹ • coreEnergy a) (fun k => coreSpatialMomentum k) j

@[simp] theorem wick_original_core_four_momentum_time (a : Parameters) :
    wickOriginalCoreFourMomentum a 0 = (a.speed : ℂ)⁻¹ • coreEnergy a := rfl

@[simp] theorem wick_original_core_four_momentum_space (a : Parameters) (j : Fin 3) :
    wickOriginalCoreFourMomentum a j.succ = coreSpatialMomentum j := rfl

theorem wick_original_core_four_momentum_component (a : Parameters) (j : Fin 4)
    (v : FiniteParticleCore) (n : ℕ) (z : ParticleConfiguration n) :
    ((wickOriginalCoreFourMomentum a j v n).val z) =
      (particleFourMomentum a n z j : ℂ) * (v n).val z := by
  cases j using Fin.cases with
  | zero =>
    change (a.speed : ℂ)⁻¹ * schwartzTotalEnergy a n (v n).val z = _
    rw [schwartzTotalEnergy_apply,particleFourMomentum_time]
    push_cast
    ring
  | succ j =>
    change schwartzTotalMomentum n j (v n).val z = _
    rw [schwartzTotalMomentum_apply,particleFourMomentum_space]

theorem wick_original_four_momentum_sector_inner (a : Parameters) (j : Fin 4)
    (u v : FiniteParticleCore) (n : ℕ) :
    inner ℂ (bosonicCoreToSector a n (u n))
      (bosonicCoreToSector a n (wickOriginalCoreFourMomentum a j v n)) =
    ∫ z, (particleFourMomentum a n z j : ℂ) *
      (star ((u n).val z) * (v n).val z) ∂particleMeasure a n := by
  change inner ℂ (particleSchwartzToHilbert a n (u n).val)
    (particleSchwartzToHilbert a n (wickOriginalCoreFourMomentum a j v n).val) = _
  rw [particle_schwartz_inner_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only
    rw [wick_original_core_four_momentum_component]
    ring)

theorem wick_original_four_momentum_vacuum_sector (a : Parameters) (j : Fin 4)
    (v : FiniteParticleCore) : wickOriginalCoreFourMomentum a j v 0 = 0 := by
  apply Subtype.ext
  ext z
  rw [wick_original_core_four_momentum_component,particleFourMomentum_zero]
  simp

theorem wick_original_four_momentum_inner_cutoff (a : Parameters) (j : Fin 4)
    (u v : FiniteParticleCore) (N : ℕ) (hu : ∀ n, N ≤ n → u n = 0) :
    inner ℂ (finiteParticleCoreToFock a u)
      (finiteParticleCoreToFock a (wickOriginalCoreFourMomentum a j v)) =
    ∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℂ) *
      (∫ p : Momentum, ∫ r, (wignerWeight a p : ℂ) * (massShell a p j : ℂ) *
        wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n) := by
  let F : ℕ → ℂ := fun n => inner ℂ (bosonicCoreToSector a n (u n))
    (bosonicCoreToSector a n (wickOriginalCoreFourMomentum a j v n))
  have hzero : F 0 = 0 := by simp [F,wick_original_four_momentum_vacuum_sector]
  have hN : F N = 0 := by simp [F,hu N le_rfl]
  have shift : (∑ n ∈ Finset.range N,F n) = ∑ n ∈ Finset.range N,F (n+1) := by
    have h := Finset.sum_range_succ' F N
    rw [Finset.sum_range_succ,hzero,hN,add_zero,add_zero] at h
    exact h
  rw [wick_original_fock_inner_range a u _ N hu]
  change (∑ n ∈ Finset.range N,F n) = _
  rw [shift]
  apply Finset.sum_congr rfl
  intro n hn
  exact (wick_original_four_momentum_sector_inner a j u v (n+1)).trans
    (wick_original_mixed_diagonal_sector_integral a n u v j).symm

theorem wick_original_four_momentum_joint_cutoff (a : Parameters) (j : Fin 4)
    (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a u)
      (finiteParticleCoreToFock a (wickOriginalCoreFourMomentum a j v)) =
    ∑ n ∈ Finset.range (wickJointCoreCutoff u v), ((n+1 : ℕ) : ℂ) *
      (∫ p : Momentum, ∫ r, (wignerWeight a p : ℂ) * (massShell a p j : ℂ) *
        wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n) := by
  apply wick_original_four_momentum_inner_cutoff
  intro n hn
  exact wickCoreCutoff_zero u n ((le_max_left _ _).trans hn)

end AASCKleinGordon
