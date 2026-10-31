import WickPhysicalTemporalKernel
import WickPhysicalMeasureSplit

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_mixed_channel_visible_frequency (a : Parameters) (n : ℕ) (k : Fin 4)
    (mixed : k=1 ∨ k=2) (p q : Momentum) (r : ParticleConfiguration n) :
    wickCoreChannelFrequency0 a n k (Fin.cons p (Fin.cons q r))+
      wickCoreChannelFrequency1 a n k (Fin.cons p (Fin.cons q r))=
        shellFrequency a p-shellFrequency a q := by
  rcases mixed with rfl|rfl
  · rfl
  · change -shellFrequency a q+shellFrequency a p=shellFrequency a p-shellFrequency a q
    abel

theorem wick_original_mixed_local_marginal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (mixed : k=1 ∨ k=2) (x : Spacetime) :
    wickCoreRaisedStressMatrix a n u v k 0 j x=
      ∫ p,∫ q,Real.fourierChar (-inner ℝ x (shellFrequency a p-shellFrequency a q)) •
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
      simp_rw [show ∀ r,ω (Fin.cons p (Fin.cons q r))=shellFrequency a p-shellFrequency a q from
        fun r => wick_mixed_channel_visible_frequency a n k mixed p q r]
      rw [wick_original_stress_pair_marginal_apply]
      change (∫ r,(Real.fourierChar (-inner ℝ x (shellFrequency a p-shellFrequency a q)) : ℂ)*
        K (Fin.cons p (Fin.cons q r)) ∂particleMeasure a n)=_
      exact integral_const_mul _ _))

theorem wick_spacetime_spatial_join_inner (τ σ : ℝ) (x y : WickSpaceSlice) :
    inner ℝ (spacetimeSpatialJoin (τ,x)) (spacetimeSpatialJoin (σ,y))=
      τ*σ+inner ℝ x y := by
  simp only [PiLp.inner_apply,Fin.sum_univ_succ,spacetimeSpatialJoin_zero,
    spacetimeSpatialJoin_succ,RCLike.inner_apply,conj_trivial]
  ring

theorem wick_mixed_spatial_phase_split (a : Parameters) (τ : ℝ) (x : WickSpaceSlice)
    (p q : Momentum) :
    (Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (τ,x))
      (shellFrequency a p-shellFrequency a q)) : ℂ)=
      (Real.fourierChar (-inner ℝ ((fourierWaveScale a) •
        (momentumEuclidean p-momentumEuclidean q)) x) : ℂ)*wickMixedTemporalPhase a τ (p,q) := by
  rw [wick_mixed_temporal_phase_actual]
  have split : spacetimeSpatialJoin (τ,x)=spacetimeSpatialJoin (0,x)+spacetimeSpatialJoin (τ,0) := by
    rw [← map_add]
    congr 1
    simp
  rw [split,inner_add_left,neg_add,AddChar.map_add_eq_mul,Circle.coe_mul]
  congr 1
  rw [shellFrequency_spacetimeSpatialJoin,shellFrequency_spacetimeSpatialJoin,← map_sub,
    wick_spacetime_spatial_join_inner]
  change (Real.fourierChar (-(0*((-shellAngularFrequency a p/(2*Real.pi))-
    (-shellAngularFrequency a q/(2*Real.pi)))+inner ℝ x
      ((fourierWaveScale a) • momentumEuclidean p-(fourierWaveScale a) • momentumEuclidean q))) : ℂ)=_
  simp only [zero_mul,zero_add,← smul_sub,real_inner_comm]

def wickPhysicalEuclideanMixedKernel (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k j : Fin 4) (τ : ℝ) : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (momentumEuclidean.symm.prodCongr momentumEuclidean.symm)
      (wickPhysicalMixedPairKernel a n u v k j τ)

theorem wick_physical_mixed_local_is_spatial_kernel (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (mixed : k=1 ∨ k=2) (τ : ℝ) (x : WickSpaceSlice) :
    wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x))=
      ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
        Real.fourierChar (-inner ℝ ((fourierWaveScale a) • (p-q)) x) •
          wickPhysicalEuclideanMixedKernel a n u v k j τ (p,q) := by
  rw [wick_original_mixed_local_marginal a n u v k j mixed,
    wick_two_wigner_integrals_weighted_volume,wick_momentum_pair_integral_euclidean]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by
    dsimp only
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun q => by
      dsimp only
      simp only [Circle.smul_def,smul_eq_mul]
      rw [wick_mixed_spatial_phase_split]
      change _ = (Real.fourierChar (-inner ℝ ((fourierWaveScale a) • (p-q)) x) : ℂ)*
        wickPhysicalMixedPairKernel a n u v k j τ (momentumEuclidean.symm p,momentumEuclidean.symm q)
      rw [wickPhysicalMixedPairKernel,
        SchwartzMap.smulLeftCLM_apply_apply (wick_physical_pair_weight_temperate a τ)]
      simp only [wickPhysicalPairWeight,ContinuousLinearEquiv.apply_symm_apply,smul_eq_mul]
      ring))

theorem wick_original_mixed_spatial_charge_diagonal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (mixed : k=1 ∨ k=2) (τ : ℝ) :
    (∫ x : WickSpaceSlice,wickCoreRaisedStressMatrix a n u v k 0 j (spacetimeSpatialJoin (τ,x)))=
      (wickSpatialFourierJacobian a : ℂ)*
        ∫ p : WickSpaceSlice,wickPhysicalEuclideanMixedKernel a n u v k j τ (p,p) := by
  simp_rw [wick_physical_mixed_local_is_spatial_kernel a n u v k j mixed]
  exact wick_original_scaled_spatial_integral a _

end AASCKleinGordon
