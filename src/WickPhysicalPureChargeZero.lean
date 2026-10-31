import WickPhysicalPureLocalFormula

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_shell_spatial_antipodal (a : Parameters) (p : Momentum) (i : Fin 3) :
    shellFrequency a p i.succ+shellFrequency a (-p) i.succ=0 := by
  rw [shellFrequency_spacetimeSpatialJoin,shellFrequency_spacetimeSpatialJoin]
  simp only [spacetimeSpatialJoin_succ,map_neg,smul_neg,PiLp.neg_apply,add_neg_cancel]

theorem wick_physical_pure_pair_kernel_antidiagonal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ) (p : Momentum) :
    wickPhysicalPurePairKernel a n u v k j τ (p,-p)=0 := by
  rw [wickPhysicalPurePairKernel,
    SchwartzMap.smulLeftCLM_apply_apply (wick_physical_pure_pair_weight_temperate a k τ),
    wick_original_stress_pair_marginal_apply]
  have hzero : (∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
      (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
        (Fin.cons p (Fin.cons (-p) r)) ∂particleMeasure a n)=0 := by
    have hz : ∀ r : ParticleConfiguration n,
        wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
          (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
            (Fin.cons p (Fin.cons (-p) r))=0 := by
      intro r
      rcases pure with rfl|rfl
      · apply wick_original_CC_kernel_zero_spatial_transfer
        intro i
        simpa only [Fin.cons_zero,Fin.cons_one] using wick_shell_spatial_antipodal a p i
      · apply wick_original_AA_kernel_zero_spatial_transfer
        intro i
        change -shellFrequency a (-p) i.succ+-shellFrequency a p i.succ=0
        have h := wick_shell_spatial_antipodal a p i
        linarith
    simp_rw [hz]
    simp
  rw [hzero,smul_zero]

theorem wick_physical_euclidean_pure_diagonal_zero (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ)
    (p : WickSpaceSlice) : wickPhysicalEuclideanPureKernel a n u v k j τ (p,p)=0 := by
  change wickPhysicalPurePairKernel a n u v k j τ
    (momentumEuclidean.symm ((wickPureReflection k (p,p)).1),
      momentumEuclidean.symm ((wickPureReflection k (p,p)).2))=0
  by_cases hk : k=0
  · rw [show wickPureReflection k (p,p)=(p,-p) by simp [wickPureReflection,hk]]
    simp only [map_neg]
    exact wick_physical_pure_pair_kernel_antidiagonal a n u v k j pure τ _
  · rw [show wickPureReflection k (p,p)=(-p,p) by simp [wickPureReflection,hk]]
    have hn : momentumEuclidean.symm p= -momentumEuclidean.symm (-p) := by simp only [map_neg,neg_neg]
    change wickPhysicalPurePairKernel a n u v k j τ
      (momentumEuclidean.symm (-p),momentumEuclidean.symm p)=0
    rw [hn]
    exact wick_physical_pure_pair_kernel_antidiagonal a n u v k j pure τ _

theorem wick_original_pure_hypersurface_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ) :
    Integrable (fun x : WickSpaceSlice =>
      wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))) := by
  let H := wickPhysicalEuclideanPureKernel a n u v k j τ
  let f := fun x : WickSpaceSlice => ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
    Real.fourierChar (-inner ℝ (p-q) x) • H (p,q)
  have hi : Integrable f := wick_actual_spatial_kernel_integrable H
  have scaled := (integrable_comp_smul_iff (volume : Measure WickSpaceSlice) f
    (fourierWaveScale_pos a).ne').mpr hi
  convert scaled using 1
  funext x
  rw [wick_physical_pure_local_is_spatial_kernel a n u v k j pure τ]
  dsimp only [f,H]
  simp only [real_inner_smul_left,real_inner_smul_right]

theorem wick_original_pure_spatial_charge_diagonal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))=
      (wickSpatialFourierJacobian a : ℂ)*
        ∫ p : WickSpaceSlice,wickPhysicalEuclideanPureKernel a n u v k j τ (p,p) := by
  simp_rw [wick_physical_pure_local_is_spatial_kernel a n u v k j pure]
  exact wick_original_scaled_spatial_integral a _

theorem wick_original_pure_hypersurface_integral_zero (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))=0 := by
  rw [wick_original_pure_spatial_charge_diagonal a n u v k j pure]
  simp_rw [wick_physical_euclidean_pure_diagonal_zero a n u v k j pure]
  simp

theorem wick_original_CC_hypersurface_integral_zero (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v 0 0 j (spacetimeSpatialJoin (τ,x)))=0 :=
  wick_original_pure_hypersurface_integral_zero a n u v 0 j (Or.inl rfl) τ

theorem wick_original_AA_hypersurface_integral_zero (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v 3 0 j (spacetimeSpatialJoin (τ,x)))=0 :=
  wick_original_pure_hypersurface_integral_zero a n u v 3 j (Or.inr rfl) τ

end AASCKleinGordon
