import WickOneParticleSourcePairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace AASCKleinGordon

/-- The Casimir multiplier of the existing joint contravariant momentum. -/
def wickInvariantMassSquared (q : FourMomentum) : ℝ :=
  q 0^2-q 1^2-q 2^2-q 3^2

theorem wick_invariant_mass_squared_continuous : Continuous wickInvariantMassSquared := by
  unfold wickInvariantMassSquared
  fun_prop

def wickAugmentedMomentum (a : Parameters) (p : Momentum) : EuclideanSpace ℝ (Fin 4) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm (Fin.cons (a.mass*a.speed) p)

@[simp] theorem wick_augmented_momentum_zero (a : Parameters) (p : Momentum) :
    wickAugmentedMomentum a p 0=a.mass*a.speed := rfl

@[simp] theorem wick_augmented_momentum_succ (a : Parameters) (p : Momentum) (j : Fin 3) :
    wickAugmentedMomentum a p j.succ=p j := rfl

theorem wick_augmented_momentum_norm_sq (a : Parameters) (p : Momentum) :
    ‖wickAugmentedMomentum a p‖^2=(a.mass*a.speed)^2+momentumSq p := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_succ,momentumSq,Real.norm_eq_abs,sq_abs]
  ring

theorem wick_augmented_momentum_norm (a : Parameters) (p : Momentum) :
    ‖wickAugmentedMomentum a p‖=energy a p/a.speed := by
  have he : (energy a p/a.speed)^2=(a.mass*a.speed)^2+momentumSq p := by
    rw [div_pow,energy_sq]
    field_simp [a.speed_pos.ne']
    <;> ring
  have hn := wick_augmented_momentum_norm_sq a p
  have hp := div_pos (energy_pos a p) a.speed_pos
  nlinarith [norm_nonneg (wickAugmentedMomentum a p)]

theorem wick_augmented_total_norm_sq (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    ‖∑ k,wickAugmentedMomentum a (x k)‖^2=
      ((n : ℝ)*a.mass*a.speed)^2+
        (particleFourMomentum a n x 1)^2+(particleFourMomentum a n x 2)^2+
          (particleFourMomentum a n x 3)^2 := by
  have he (j : Fin 4) : (∑ k,wickAugmentedMomentum a (x k)) j=
      ∑ k,wickAugmentedMomentum a (x k) j :=
    map_sum (PiLp.projₗ (𝕜:=ℝ) 2 (fun _ : Fin 4 => ℝ) j) _ _
  have hp (j : Fin 3) : particleFourMomentum a n x j.succ=∑ k,x k j := by
    rw [particleFourMomentum_space,totalMomentumCLM_apply]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_succ,he,wick_augmented_momentum_zero,wick_augmented_momentum_succ,
    Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [show (1 : Fin 4)=(0 : Fin 3).succ by rfl,
    show (2 : Fin 4)=(1 : Fin 3).succ by rfl,
    show (3 : Fin 4)=(2 : Fin 3).succ by rfl,hp,hp,hp]
  simp only [show (Fin.succ (0 : Fin 2) : Fin 3)=1 by rfl,
    show (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3)=2 by rfl]
  ring

/-- Actual multiparticle lower bound; no spectral-isolation premise is supplied. -/
theorem wick_particle_invariant_mass_lower_bound (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    ((n : ℝ)*a.mass*a.speed)^2 ≤ wickInvariantMassSquared (particleFourMomentum a n x) := by
  have hn : ‖∑ k,wickAugmentedMomentum a (x k)‖ ≤ particleFourMomentum a n x 0 := by
    calc
      _ ≤ ∑ k,‖wickAugmentedMomentum a (x k)‖ := norm_sum_le _ _
      _ = _ := by simp [wick_augmented_momentum_norm,particleFourMomentum_time,
        particleTotalEnergy,Finset.sum_div]
  have ht : 0≤particleFourMomentum a n x 0 := (norm_nonneg _).trans hn
  have hs := (sq_le_sq₀ (norm_nonneg _) ht).mpr hn
  rw [wick_augmented_total_norm_sq] at hs
  dsimp only [wickInvariantMassSquared]
  nlinarith

theorem wick_particle_one_invariant_mass (a : Parameters) (x : ParticleConfiguration 1) :
    wickInvariantMassSquared (particleFourMomentum a 1 x)=a.mass^2*a.speed^2 := by
  have hp : particleFourMomentum a 1 x=massShell a (x 0) := by simp [particleFourMomentum]
  rw [hp]
  have h := massShell_on_shell a (x 0)
  dsimp only [wickInvariantMassSquared,minkowskiDot] at *
  nlinarith

theorem wick_particle_higher_invariant_mass_gap (a : Parameters) (n : ℕ) (hn : 2≤n)
    (x : ParticleConfiguration n) :
    4*a.mass^2*a.speed^2 ≤ wickInvariantMassSquared (particleFourMomentum a n x) := by
  have h := wick_particle_invariant_mass_lower_bound a n x
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hmc := mul_pos a.mass_pos a.speed_pos
  have h2 : 0≤2*a.mass*a.speed :=
    mul_nonneg (mul_nonneg (by norm_num) a.mass_pos.le) a.speed_pos.le
  have hn0 : 0≤(n : ℝ)*a.mass*a.speed :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) a.mass_pos.le) a.speed_pos.le
  have hlin : 2*a.mass*a.speed≤(n : ℝ)*a.mass*a.speed := by
    nlinarith [mul_le_mul_of_nonneg_right hnR hmc.le]
  have hs : (2*a.mass*a.speed)^2≤((n : ℝ)*a.mass*a.speed)^2 :=
    (sq_le_sq₀ h2 hn0).mpr hlin
  nlinarith

end AASCKleinGordon
