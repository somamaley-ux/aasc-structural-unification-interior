import KGReferenceM3Vacuum

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace AASCKleinGordon

def spatialFourEuclidean (q : FourMomentum) : EuclideanSpace ℝ (Fin 3) :=
  momentumEuclidean (fun j => q j.succ)

def futureMomentumCone : Set FourMomentum := {q | ‖spatialFourEuclidean q‖≤q 0}

def particleFourMomentum (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) : FourMomentum :=
  ∑ i,massShell a (x i)

theorem particleFourMomentum_time (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleFourMomentum a n x 0=particleTotalEnergy a n x/a.speed := by
  simp [particleFourMomentum,massShell,particleTotalEnergy,Finset.sum_div]

theorem particleFourMomentum_space (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) (j : Fin 3) :
    particleFourMomentum a n x j.succ=totalMomentumCLM n j x := by
  fin_cases j <;> simp [particleFourMomentum,massShell,totalMomentumCLM_apply]

theorem particleFourMomentum_continuous (a : Parameters) (n : ℕ) :
    Continuous (particleFourMomentum a n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [particleFourMomentum_time] using (particleTotalEnergy_continuous a n).div_const a.speed
  · simpa only [particleFourMomentum_space] using (totalMomentumCLM n j).continuous

theorem particleFourMomentum_permutation (a : Parameters) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleFourMomentum a n (particlePermutation n σ x)=particleFourMomentum a n x := by
  unfold particleFourMomentum
  simp only [particlePermutation_apply]
  exact Equiv.sum_comp σ.symm (fun i => massShell a (x i))

theorem shell_spatial_norm_le_energy (a : Parameters) (p : Momentum) :
    ‖momentumEuclidean p‖≤energy a p/a.speed := by
  have h : (a.speed*‖momentumEuclidean p‖)^2≤energy a p^2 := by
    rw [mul_pow,momentumEuclidean_norm_sq,energy_sq]
    nlinarith [sq_nonneg a.mass,sq_nonneg (a.speed^2)]
  have hn : a.speed*‖momentumEuclidean p‖≤energy a p :=
    (sq_le_sq₀ (mul_nonneg a.speed_pos.le (norm_nonneg _)) (energy_pos a p).le).mp h
  exact (le_div_iff₀ a.speed_pos).mpr (by nlinarith)

theorem particleFourMomentum_spatial (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    spatialFourEuclidean (particleFourMomentum a n x)=∑ i,momentumEuclidean (x i) := by
  rw [spatialFourEuclidean,← map_sum]
  congr 1
  funext j
  rw [particleFourMomentum_space]
  simp [totalMomentumCLM_apply]

theorem particleFourMomentum_mem_futureCone (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleFourMomentum a n x∈futureMomentumCone := by
  change ‖spatialFourEuclidean (particleFourMomentum a n x)‖≤_
  rw [particleFourMomentum_spatial,particleFourMomentum_time]
  calc
    _ ≤ ∑ i,‖momentumEuclidean (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i,energy a (x i)/a.speed := Finset.sum_le_sum (fun i _ => shell_spatial_norm_le_energy a (x i))
    _ = _ := by simp only [particleTotalEnergy,Finset.sum_div]

theorem particleFourMomentum_zero (a : Parameters) (x : ParticleConfiguration 0) :
    particleFourMomentum a 0 x=0 := by simp [particleFourMomentum]

end AASCKleinGordon
