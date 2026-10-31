import WickPhysicalPureTemporalKernel
import WickPhysicalMeasureSplit

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_original_pure_local_marginal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (x : Spacetime) :
    wickCoreRaisedStressMatrix a n u v k 0 j x=
      ∫ p,∫ q,Real.fourierChar (-inner ℝ x ((if k=0 then shellFrequency a p+shellFrequency a q else -shellFrequency a q-shellFrequency a p))) •
        wickOriginalStressPairMarginal a n u v k j (p,q) ∂wignerMeasure a ∂wignerMeasure a := by
  let K := wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
    (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
  let ω := fun z => wickCoreChannelFrequency0 a n k z+wickCoreChannelFrequency1 a n k z
  have hi := wickLocalMatrix_integrable a (n+2) ω
    (((wickCoreChannelFrequency0_temperate a n k).add
      (wickCoreChannelFrequency1_temperate a n k)).1.continuous) K x
  change (∫ z,Real.fourierChar (-inner ℝ x (ω z)) • K z ∂particleMeasure a (n+2))=_
  rw [wick_particle_integral_two_visible a n _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by
      dsimp only
      simp_rw [show ∀ r,ω (Fin.cons p (Fin.cons q r))=(if k=0 then shellFrequency a p+shellFrequency a q else -shellFrequency a q-shellFrequency a p) from
        fun r => wick_pure_channel_visible_frequency a n k pure p q r]
      rw [wick_original_stress_pair_marginal_apply]
      change (∫ r,(Real.fourierChar (-inner ℝ x ((if k=0 then shellFrequency a p+shellFrequency a q else -shellFrequency a q-shellFrequency a p))) : ℂ)*
        K (Fin.cons p (Fin.cons q r)) ∂particleMeasure a n)=_
      exact integral_const_mul _ _))

theorem wick_pure_spatial_phase_split (a : Parameters) (k : Fin 4) (τ : ℝ)
    (x : WickSpaceSlice) (p q : Momentum) :
    (Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (τ,x))
      (if k=0 then shellFrequency a p+shellFrequency a q
        else -shellFrequency a q-shellFrequency a p)) : ℂ)=
      (Real.fourierChar (-inner ℝ ((fourierWaveScale a) •
        (if k=0 then momentumEuclidean p+momentumEuclidean q
          else -momentumEuclidean q-momentumEuclidean p)) x) : ℂ)*
            wickPureTemporalPhase a k τ (p,q) := by
  rw [wick_pure_temporal_phase_actual]
  have split : spacetimeSpatialJoin (τ,x)=spacetimeSpatialJoin (0,x)+spacetimeSpatialJoin (τ,0) := by
    rw [← map_add]
    congr 1
    simp
  rw [split,inner_add_left,neg_add,AddChar.map_add_eq_mul,Circle.coe_mul]
  congr 1
  by_cases hk : k=0
  · simp only [if_pos hk,shellFrequency_spacetimeSpatialJoin,← map_add]
    change (Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (0,x))
      (spacetimeSpatialJoin (_,
      ((fourierWaveScale a) • momentumEuclidean p+(fourierWaveScale a) • momentumEuclidean q)))) : ℂ)=_
    rw [wick_spacetime_spatial_join_inner]
    simp only [zero_mul,zero_add,map_add,smul_add,real_inner_comm]
  · simp only [if_neg hk,shellFrequency_spacetimeSpatialJoin,← map_neg,← map_sub]
    change (Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (0,x))
      (spacetimeSpatialJoin (_,
      (-((fourierWaveScale a) • momentumEuclidean q)-(fourierWaveScale a) • momentumEuclidean p)))) : ℂ)=_
    rw [wick_spacetime_spatial_join_inner]
    simp only [zero_mul,zero_add,map_neg,map_sub,smul_sub,smul_neg,real_inner_comm]

theorem wick_physical_pure_local_unreflected (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ) (x : WickSpaceSlice) :
    wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))=
      ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
        (Real.fourierChar (-inner ℝ ((fourierWaveScale a) •
          (if k=0 then p+q else -q-p)) x) : ℂ)*
          wickPhysicalPurePairKernel a n u v k j τ
            (momentumEuclidean.symm p,momentumEuclidean.symm q) := by
  rw [wick_original_pure_local_marginal a n u v k j pure,
    wick_two_wigner_integrals_weighted_volume,wick_momentum_pair_integral_euclidean]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by
      dsimp only
      simp only [Circle.smul_def,smul_eq_mul]
      rw [wick_pure_spatial_phase_split]
      rw [wickPhysicalPurePairKernel,
        SchwartzMap.smulLeftCLM_apply_apply (wick_physical_pure_pair_weight_temperate a k τ)]
      simp only [wickPhysicalPurePairWeight,ContinuousLinearEquiv.apply_symm_apply,smul_eq_mul]
      ring))

theorem wick_physical_pure_local_is_spatial_kernel (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (pure : k=0 ∨ k=3) (τ : ℝ) (x : WickSpaceSlice) :
    wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))=
      ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
        Real.fourierChar (-inner ℝ ((fourierWaveScale a) • (p-q)) x) •
          wickPhysicalEuclideanPureKernel a n u v k j τ (p,q) := by
  rw [wick_physical_pure_local_unreflected a n u v k j pure τ]
  by_cases hk : k=0
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => by
      dsimp only
      rw [← integral_neg_eq_self (fun q : WickSpaceSlice =>
        (Real.fourierChar (-inner ℝ ((fourierWaveScale a) •
          (if k=0 then p+q else -q-p)) x) : ℂ)*
            wickPhysicalPurePairKernel a n u v k j τ
              (momentumEuclidean.symm p,momentumEuclidean.symm q)) volume]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        dsimp only
        change _=(Real.fourierChar (-inner ℝ ((fourierWaveScale a) • (p-q)) x) : ℂ)*
          wickPhysicalPurePairKernel a n u v k j τ
            (momentumEuclidean.symm ((wickPureReflection k (p,q)).1),
              momentumEuclidean.symm ((wickPureReflection k (p,q)).2))
        rw [show wickPureReflection k (p,q)=(p,-q) by simp [wickPureReflection,hk]]
        simp only [if_pos hk,sub_eq_add_neg]))
  · rw [← integral_neg_eq_self (fun p : WickSpaceSlice => ∫ q : WickSpaceSlice,
      (Real.fourierChar (-inner ℝ ((fourierWaveScale a) •
        (if k=0 then p+q else -q-p)) x) : ℂ)*
          wickPhysicalPurePairKernel a n u v k j τ
            (momentumEuclidean.symm p,momentumEuclidean.symm q)) volume]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => by
      dsimp only
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        dsimp only
        change _=(Real.fourierChar (-inner ℝ ((fourierWaveScale a) • (p-q)) x) : ℂ)*
          wickPhysicalPurePairKernel a n u v k j τ
            (momentumEuclidean.symm ((wickPureReflection k (p,q)).1),
              momentumEuclidean.symm ((wickPureReflection k (p,q)).2))
        rw [show wickPureReflection k (p,q)=(-p,q) by simp [wickPureReflection,hk]]
        simp only [if_neg hk,sub_neg_eq_add]
        congr 3
        abel))

end AASCKleinGordon
