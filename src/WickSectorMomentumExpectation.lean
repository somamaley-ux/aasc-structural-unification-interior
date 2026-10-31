import WickPhysicalTwoMixedCharges
import KGJointMomentumCone
import KGCoreEnergy
import KGWickFiniteCoreKernelAttachment

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_original_mixed_state_diagonal (n : ℕ) (u v : FiniteParticleCore)
    (p : Momentum) (r : ParticleConfiguration n) :
    wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) =
      star ((u (n+1)).val (Fin.cons p r)) * (v (n+1)).val (Fin.cons p r) := by
  simp [wickCoreChannelStateKernel,wickMixedStateKernel_apply]

theorem wick_shell_coordinate_temperate (a : Parameters) (n : ℕ) (i : Fin n) (j : Fin 4) :
    (fun z : ParticleConfiguration n => (massShell a (z i) j : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp
    ((ContinuousLinearMap.proj j : FourMomentum →L[ℝ] ℝ).hasTemperateGrowth.comp
      ((massShell_temperate a).comp
        (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum).hasTemperateGrowth))

def wickShellCoordinateSchwartz (a : Parameters) (n : ℕ) (i : Fin n) (j : Fin 4)
    (v : 𝓢(ParticleConfiguration n,ℂ)) : 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z : ParticleConfiguration n => (massShell a (z i) j : ℂ)) v

@[simp] theorem wick_shell_coordinate_schwartz_apply (a : Parameters) (n : ℕ) (i : Fin n)
    (j : Fin 4) (v : 𝓢(ParticleConfiguration n,ℂ)) (z : ParticleConfiguration n) :
    wickShellCoordinateSchwartz a n i j v z = (massShell a (z i) j : ℂ) * v z :=
  SchwartzMap.smulLeftCLM_apply_apply (wick_shell_coordinate_temperate a n i j) v z

theorem wick_shell_pair_integrable (a : Parameters) (n : ℕ) (i : Fin n) (j : Fin 4)
    (u v : 𝓢(ParticleConfiguration n,ℂ)) :
    Integrable (fun z => (massShell a (z i) j : ℂ) * (star (u z) * v z))
      (particleMeasure a n) := by
  have h := schwartz_pair_integrable (particleMeasure a n) u (wickShellCoordinateSchwartz a n i j v)
  simpa only [wick_shell_coordinate_schwartz_apply,mul_left_comm,mul_assoc] using h

theorem wick_bosonic_shell_integral_equal (a : Parameters) (n : ℕ) (i : Fin (n+1))
    (j : Fin 4) (u v : bosonicSchwartz (n+1)) :
    (∫ z, (massShell a (z i) j : ℂ) * (star (u.val z) * v.val z) ∂particleMeasure a (n+1)) =
      ∫ z, (massShell a (z 0) j : ℂ) * (star (u.val z) * v.val z) ∂particleMeasure a (n+1) := by
  let σ : Equiv.Perm (Fin (n+1)) := Equiv.swap 0 i
  have h := (particlePermutation_preserves_measure a (n+1) σ).integral_comp
    (particlePermutation (n+1) σ).measurableEmbedding
    (fun z => (massShell a (z 0) j : ℂ) * (star (u.val z) * v.val z))
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    have hu := u.property σ.symm z
    have hv := v.property σ.symm z
    have hz : particlePermutation (n+1) σ z = fun k => z (σ.symm k) :=
      funext (particlePermutation_apply (n+1) σ z)
    dsimp only
    rw [hz,hu,hv]
    simp [σ])

theorem wick_bosonic_total_momentum_integral (a : Parameters) (n : ℕ) (j : Fin 4)
    (u v : bosonicSchwartz (n+1)) :
    (∫ z, (particleFourMomentum a (n+1) z j : ℂ) * (star (u.val z) * v.val z)
      ∂particleMeasure a (n+1)) =
    ((n+1 : ℕ) : ℂ) * ∫ z, (massShell a (z 0) j : ℂ) * (star (u.val z) * v.val z)
      ∂particleMeasure a (n+1) := by
  have point (z : ParticleConfiguration (n+1)) :
      (particleFourMomentum a (n+1) z j : ℂ) * (star (u.val z) * v.val z) =
      ∑ i : Fin (n+1), (massShell a (z i) j : ℂ) * (star (u.val z) * v.val z) := by
    simp [particleFourMomentum,Finset.sum_mul]
  simp_rw [point]
  rw [integral_finset_sum _ (fun i _ => wick_shell_pair_integrable a (n+1) i j u.val v.val)]
  simp_rw [wick_bosonic_shell_integral_equal a n _ j u v]
  simp

theorem wick_original_mixed_diagonal_sector_integral (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (j : Fin 4) :
    ((n+1 : ℕ) : ℂ) * (∫ p : Momentum, ∫ r,
      (wignerWeight a p : ℂ) * (massShell a p j : ℂ) *
        wickCoreChannelStateKernel n u v 1 (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n) =
    ∫ z, (particleFourMomentum a (n+1) z j : ℂ) *
      (star ((u (n+1)).val z) * (v (n+1)).val z) ∂particleMeasure a (n+1) := by
  rw [wick_bosonic_total_momentum_integral]
  congr 1
  rw [wick_particle_integral_head a n _
    (wick_shell_pair_integrable a (n+1) 0 j (u (n+1)).val (v (n+1)).val),
    wigner_integral_eq_weighted_volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun r => by
      dsimp only
      rw [wick_original_mixed_state_diagonal]
      simp only [Fin.cons_zero]
      ring))

end AASCKleinGordon
