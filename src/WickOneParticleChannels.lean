import WickActualElasticSymbol

noncomputable section
set_option maxHeartbeats 2200000
open MeasureTheory
open scoped BigOperators SchwartzMap DirectSum
namespace AASCKleinGordon
open SchwartzOperations

/-- Abbreviation for the existing original core injection; no new carrier. -/
abbrev wickOneParticleCore (f : bosonicSchwartz 1) : FiniteParticleCore :=
  DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f

theorem wick_one_particle_off_sector (f : bosonicSchwartz 1) (n : ℕ) (h : n ≠ 1) :
    wickOneParticleCore f n = 0 := by
  simp [wickOneParticleCore,DirectSum.lof_eq_of,DirectSum.of_apply,h,Ne.symm h]

theorem wick_one_particle_at_sector (f : bosonicSchwartz 1) : wickOneParticleCore f 1=f := by
  simp [wickOneParticleCore,DirectSum.lof_eq_of,DirectSum.of_apply]

theorem wick_one_particle_CC_state_zero (f g : bosonicSchwartz 1) (n : ℕ) :
    wickCoreChannelStateKernel n (wickOneParticleCore f) (wickOneParticleCore g) 0=0 := by
  have hz := wick_one_particle_off_sector f (n+2) (by omega)
  have hAA : wickAAStateKernel n (wickOneParticleCore g n).val (wickOneParticleCore f (n+2)).val=0 := by
    ext z
    simp [wickAAStateKernel_apply,hz]
  change conjugateSchwartzCLM _=0
  rw [hAA,map_zero]

theorem wick_one_particle_AA_state_zero (f g : bosonicSchwartz 1) (n : ℕ) :
    wickCoreChannelStateKernel n (wickOneParticleCore f) (wickOneParticleCore g) 3=0 := by
  have hz := wick_one_particle_off_sector g (n+2) (by omega)
  change wickAAStateKernel n (wickOneParticleCore f n).val (wickOneParticleCore g (n+2)).val=0
  ext z
  simp [wickAAStateKernel_apply,hz]

theorem wick_one_particle_higher_state_zero (f g : bosonicSchwartz 1) (n : ℕ) (hn : n ≠ 0)
    (k : Fin 4) :
    wickCoreChannelStateKernel n (wickOneParticleCore f) (wickOneParticleCore g) k=0 := by
  have hz := wick_one_particle_off_sector f (n+1) (by omega)
  have hmix : wickMixedStateKernel n (wickOneParticleCore f (n+1)).val
      (wickOneParticleCore g (n+1)).val=0 := by
    ext z
    simp [wickMixedStateKernel_apply,hz]
  fin_cases k
  · exact wick_one_particle_CC_state_zero f g n
  · exact hmix
  · exact hmix
  · exact wick_one_particle_AA_state_zero f g n

theorem wick_core_stress_zero_of_state_zero (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k i j : Fin 4) (hz : wickCoreChannelStateKernel n u v k=0) (x : Spacetime) :
    wickCoreRaisedStressMatrix a n u v k i j x=0 := by
  have hk : wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
      (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) i j=0 := by
    ext z
    rw [wick_raised_stress_kernel_apply a (n+2) _ _
      (wickCoreChannelFrequency0_temperate a n k) (wickCoreChannelFrequency1_temperate a n k)]
    simp [hz]
  simp [wickCoreRaisedStressMatrix,wickRaisedStressLocalMatrix,hk,wickLocalMatrix]

theorem wick_one_particle_mixed_channels_equal (a : Parameters) (f g : bosonicSchwartz 1)
    (i j : Fin 4) (x : Spacetime) :
    wickCoreRaisedStressMatrix a 0 (wickOneParticleCore f) (wickOneParticleCore g) 2 i j x=
      wickCoreRaisedStressMatrix a 0 (wickOneParticleCore f) (wickOneParticleCore g) 1 i j x := by
  unfold wickCoreRaisedStressMatrix wickRaisedStressLocalMatrix wickLocalMatrix
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [wick_raised_stress_kernel_apply a 2 _ _
      (wickCoreChannelFrequency0_temperate a 0 2) (wickCoreChannelFrequency1_temperate a 0 2)]
    rw [wick_raised_stress_kernel_apply a 2 _ _
      (wickCoreChannelFrequency0_temperate a 0 1) (wickCoreChannelFrequency1_temperate a 0 1)]
    change Real.fourierChar (-inner ℝ x (-shellFrequency a (z 1)+shellFrequency a (z 0))) •
      (wickRaisedStressSymbol a (-shellFrequency a (z 1)) (shellFrequency a (z 0)) i j*
        wickCoreChannelStateKernel 0 (wickOneParticleCore f) (wickOneParticleCore g) 1 z)=_
    rw [add_comm (-shellFrequency a (z 1)),wick_same_stress_symbol_swap]
    rfl

/-- Actual original finite channel expansion specialized to the one-particle
subspace, with its original cutoff retained in the proof. -/
theorem wick_original_one_particle_stress_two_mixed (a : Parameters) (s : ℝ)
    (f g : bosonicSchwartz 1) (i j : Fin 4) (x : Spacetime) :
    originalWickScalarStressRaisedMatrix a s (wickOneParticleCore f) (wickOneParticleCore g) i j x=
      2*(s : ℂ)^2*wickCoreRaisedStressMatrix a 0 (wickOneParticleCore f) (wickOneParticleCore g) 1 i j x := by
  classical
  rw [original_wick_raised_stress_channel_expansion]
  rw [Finset.product_eq_sprod,Finset.sum_product]
  have h0 : 0 < wickJointCoreCutoff (wickOneParticleCore f) (wickOneParticleCore g) := by
    dsimp [wickJointCoreCutoff,wickCoreCutoff]
    omega
  rw [Finset.sum_eq_single 0]
  · rw [Fin.sum_univ_four]
    rw [wick_core_stress_zero_of_state_zero a 0 _ _ 0 i j (wick_one_particle_CC_state_zero f g 0),
      wick_core_stress_zero_of_state_zero a 0 _ _ 3 i j (wick_one_particle_AA_state_zero f g 0),
      wick_one_particle_mixed_channels_equal]
    have hc : wickCoreChannelCoefficient 0 2=1 := by
      norm_num [wickCoreChannelCoefficient,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    rw [hc]
    norm_num [wickCoreChannelCoefficient]
    ring
  · intro n hn hn0
    apply Finset.sum_eq_zero
    intro k hk
    rw [wick_core_stress_zero_of_state_zero a n _ _ k i j
      (wick_one_particle_higher_state_zero f g n hn0 k),mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr h0)).elim

end AASCKleinGordon
