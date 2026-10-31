import WickPhysicalPairMarginal
import WickTranslationBilocalTransport

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickMixedTemporalPhase (a : Parameters) (τ : ℝ) (z : Momentum × Momentum) : ℂ :=
  eventTranslationPhase a (spacetimeSpatialJoin (τ,0)) z.1 *
    star (eventTranslationPhase a (spacetimeSpatialJoin (τ,0)) z.2)

theorem wick_mixed_temporal_phase_temperate (a : Parameters) (τ : ℝ) :
    (wickMixedTemporalPhase a τ).HasTemperateGrowth :=
  ((eventTranslationPhase_temperate a _).comp
    (ContinuousLinearMap.fst ℝ Momentum Momentum).hasTemperateGrowth).mul
      (((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp
        (eventTranslationPhase_temperate a _)).comp
          (ContinuousLinearMap.snd ℝ Momentum Momentum).hasTemperateGrowth)

theorem wick_mixed_temporal_phase_actual (a : Parameters) (τ : ℝ) (p q : Momentum) :
    wickMixedTemporalPhase a τ (p,q)=
      (Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (τ,0))
        (shellFrequency a p-shellFrequency a q)) : ℂ) := by
  rw [wickMixedTemporalPhase,← wick_plane_phase_shell,← wick_plane_phase_shell,
    ← wick_plane_phase_neg]
  unfold wickPlanePhase
  simp only [sub_eq_add_neg,inner_add_right,neg_add,AddChar.map_add_eq_mul,Circle.coe_mul]

theorem wick_mixed_temporal_phase_diagonal (a : Parameters) (τ : ℝ) (p : Momentum) :
    wickMixedTemporalPhase a τ (p,p)=1 := by
  rw [wick_mixed_temporal_phase_actual]
  simp only [sub_self,inner_zero_right,neg_zero,AddChar.map_zero_eq_one,Circle.coe_one]

def wickPhysicalPairWeight (a : Parameters) (τ : ℝ) (z : Momentum × Momentum) : ℂ :=
  (wignerWeight a z.1 : ℂ)*(wignerWeight a z.2 : ℂ)*wickMixedTemporalPhase a τ z

theorem wick_physical_pair_weight_temperate (a : Parameters) (τ : ℝ) :
    (wickPhysicalPairWeight a τ).HasTemperateGrowth :=
  (((wick_wigner_weight_complex_temperate a).comp
    (ContinuousLinearMap.fst ℝ Momentum Momentum).hasTemperateGrowth).mul
      ((wick_wigner_weight_complex_temperate a).comp
        (ContinuousLinearMap.snd ℝ Momentum Momentum).hasTemperateGrowth)).mul
          (wick_mixed_temporal_phase_temperate a τ)

def wickPhysicalMixedPairKernel (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k j : Fin 4) (τ : ℝ) : 𝓢(Momentum × Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wickPhysicalPairWeight a τ)
    (wickOriginalStressPairMarginal a n u v k j)

theorem wick_physical_mixed_pair_kernel_apply (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k j : Fin 4) (τ : ℝ) (p q : Momentum) :
    wickPhysicalMixedPairKernel a n u v k j τ (p,q)=
      (wignerWeight a p : ℂ)*(wignerWeight a q : ℂ)*wickMixedTemporalPhase a τ (p,q)*
        ∫ r,wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n k)
          (wickCoreChannelFrequency1 a n k) (wickCoreChannelStateKernel n u v k) 0 j
          (Fin.cons p (Fin.cons q r)) ∂particleMeasure a n := by
  rw [wickPhysicalMixedPairKernel,
    SchwartzMap.smulLeftCLM_apply_apply (wick_physical_pair_weight_temperate a τ),
    wick_original_stress_pair_marginal_apply]
  rfl

end AASCKleinGordon
