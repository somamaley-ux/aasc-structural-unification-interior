import WickPhysicalMixedLocalFormula

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_physical_euclidean_mixed_diagonal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (τ : ℝ) (p : WickSpaceSlice) :
    wickPhysicalEuclideanMixedKernel a n u v k j τ (p,p)=
      (wignerWeight a (momentumEuclidean.symm p) : ℂ)^2*
        ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
          (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
          (Fin.cons (momentumEuclidean.symm p) (Fin.cons (momentumEuclidean.symm p) r))
            ∂particleMeasure a n := by
  change wickPhysicalMixedPairKernel a n u v k j τ
    (momentumEuclidean.symm p,momentumEuclidean.symm p)=_
  rw [wick_physical_mixed_pair_kernel_apply,wick_mixed_temporal_phase_diagonal]
  ring

theorem wick_original_mixed_hypersurface_integral (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (mixed : k=1 ∨ k=2) (τ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))=
      (wickSpatialFourierJacobian a : ℂ)*∫ p : Momentum,(wignerWeight a p : ℂ)^2*
        ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
          (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
          (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n := by
  rw [wick_original_mixed_spatial_charge_diagonal a n u v k j mixed τ,
    wick_momentum_integral_euclidean]
  apply congrArg ((wickSpatialFourierJacobian a : ℂ)* ·)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => wick_physical_euclidean_mixed_diagonal a n u v k j τ p)

theorem wick_original_mixed_hypersurface_time_independent (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (mixed : k=1 ∨ k=2) (τ σ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))=
      ∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (σ,x)) := by
  rw [wick_original_mixed_hypersurface_integral a n u v k j mixed τ,
    wick_original_mixed_hypersurface_integral a n u v k j mixed σ]

theorem wick_original_mixed_hypersurface_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (mixed : k=1 ∨ k=2) (τ : ℝ) :
    Integrable (fun x : WickSpaceSlice =>
      wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))) := by
  let H := wickPhysicalEuclideanMixedKernel a n u v k j τ
  let f := fun x : WickSpaceSlice => ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
    Real.fourierChar (-inner ℝ (p-q) x) • H (p,q)
  have hi : Integrable f := wick_actual_spatial_kernel_integrable H
  have scaled := (integrable_comp_smul_iff (volume : Measure WickSpaceSlice) f
    (fourierWaveScale_pos a).ne').mpr hi
  convert scaled using 1
  funext x
  rw [wick_physical_mixed_local_is_spatial_kernel a n u v k j mixed τ]
  dsimp only [f,H]
  simp only [real_inner_smul_left,real_inner_smul_right]

theorem wick_physical_euclidean_mixed_diagonal_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (τ : ℝ) :
    Integrable (fun p : WickSpaceSlice => wickPhysicalEuclideanMixedKernel a n u v k j τ (p,p)) := by
  have slice := wick_schwartz_partial_slice_integrable (volume : Measure WickSpaceSlice)
    (wickTransferKernelCLM (wickPhysicalEuclideanMixedKernel a n u v k j τ)) 0
  change Integrable (fun p : WickSpaceSlice =>
    wickPhysicalEuclideanMixedKernel a n u v k j τ (p,p-0)) at slice
  simpa only [sub_zero] using slice

theorem wick_original_mixed_diagonal_momentum_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) :
    Integrable (fun p : Momentum => (wignerWeight a p : ℂ)^2*
      ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
        (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
        (Fin.cons p (Fin.cons p r)) ∂particleMeasure a n) := by
  apply (wick_momentum_euclidean_inverse_volume.integrable_comp_emb
    momentumEuclidean.symm.toHomeomorph.measurableEmbedding).mp
  simpa only [Function.comp_def,← wick_physical_euclidean_mixed_diagonal a n u v k j 0] using
    wick_physical_euclidean_mixed_diagonal_integrable a n u v k j 0

end AASCKleinGordon
