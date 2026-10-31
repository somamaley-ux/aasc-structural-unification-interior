import WickPhysicalTemporalKernel
import WickPhysicalMixedLocalFormula
import WickOriginalChargeKernels

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickPureTemporalPhase (a : Parameters) (k : Fin 4) (τ : ℝ)
    (z : Momentum × Momentum) : ℂ :=
  if k=0 then eventTranslationPhase a (spacetimeSpatialJoin (τ,0)) z.1 *
    eventTranslationPhase a (spacetimeSpatialJoin (τ,0)) z.2
  else star (eventTranslationPhase a (spacetimeSpatialJoin (τ,0)) z.2) *
    star (eventTranslationPhase a (spacetimeSpatialJoin (τ,0)) z.1)

theorem wick_pure_temporal_phase_temperate (a : Parameters) (k : Fin 4) (τ : ℝ) :
    (wickPureTemporalPhase a k τ).HasTemperateGrowth := by
  let f := (eventTranslationPhase_temperate a (spacetimeSpatialJoin (τ,0))).comp
    (ContinuousLinearMap.fst ℝ Momentum Momentum).hasTemperateGrowth
  let g := (eventTranslationPhase_temperate a (spacetimeSpatialJoin (τ,0))).comp
    (ContinuousLinearMap.snd ℝ Momentum Momentum).hasTemperateGrowth
  by_cases hk : k=0
  · unfold wickPureTemporalPhase
    simp only [if_pos hk]
    exact f.mul g
  · unfold wickPureTemporalPhase
    simp only [if_neg hk]
    exact
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp g).mul
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp f)

theorem wick_pure_channel_visible_frequency (a : Parameters) (n : ℕ) (k : Fin 4)
    (pure : k=0 ∨ k=3) (p q : Momentum) (r : ParticleConfiguration n) :
    wickCoreChannelFrequency0 a n k (Fin.cons p (Fin.cons q r))+
      wickCoreChannelFrequency1 a n k (Fin.cons p (Fin.cons q r))=
        if k=0 then shellFrequency a p+shellFrequency a q
        else -shellFrequency a q-shellFrequency a p := by
  rcases pure with rfl|rfl
  · simp only [if_pos rfl]; rfl
  · simp only [show (3:Fin 4)≠0 by decide,if_false]
    change -shellFrequency a q+-shellFrequency a p=_
    abel

theorem wick_pure_temporal_phase_actual (a : Parameters) (k : Fin 4) (τ : ℝ)
    (p q : Momentum) :
    wickPureTemporalPhase a k τ (p,q)=
      (Real.fourierChar (-inner ℝ (spacetimeSpatialJoin (τ,0))
        (if k=0 then shellFrequency a p+shellFrequency a q
        else -shellFrequency a q-shellFrequency a p)) : ℂ) := by
  by_cases hk : k=0
  · simp only [wickPureTemporalPhase,if_pos hk]
    rw [← wick_plane_phase_shell,← wick_plane_phase_shell]
    simp only [wickPlanePhase,inner_add_right,neg_add,AddChar.map_add_eq_mul,Circle.coe_mul]
  · simp only [wickPureTemporalPhase,if_neg hk]
    rw [← wick_plane_phase_shell,← wick_plane_phase_shell,← wick_plane_phase_neg,
      ← wick_plane_phase_neg]
    simp only [wickPlanePhase,sub_eq_add_neg,inner_add_right,neg_add,
      AddChar.map_add_eq_mul,Circle.coe_mul]

def wickPhysicalPurePairWeight (a : Parameters) (k : Fin 4) (τ : ℝ)
    (z : Momentum × Momentum) : ℂ :=
  (wignerWeight a z.1 : ℂ)*(wignerWeight a z.2 : ℂ)*wickPureTemporalPhase a k τ z

theorem wick_physical_pure_pair_weight_temperate (a : Parameters) (k : Fin 4) (τ : ℝ) :
    (wickPhysicalPurePairWeight a k τ).HasTemperateGrowth :=
  (((wick_wigner_weight_complex_temperate a).comp
    (ContinuousLinearMap.fst ℝ Momentum Momentum).hasTemperateGrowth).mul
      ((wick_wigner_weight_complex_temperate a).comp
        (ContinuousLinearMap.snd ℝ Momentum Momentum).hasTemperateGrowth)).mul
          (wick_pure_temporal_phase_temperate a k τ)

def wickPhysicalPurePairKernel (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k j : Fin 4) (τ : ℝ) : 𝓢(Momentum × Momentum,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wickPhysicalPurePairWeight a k τ)
    (wickOriginalStressPairMarginal a n u v k j)

def wickPureReflection (k : Fin 4) :
    (WickSpaceSlice × WickSpaceSlice) ≃L[ℝ] (WickSpaceSlice × WickSpaceSlice) :=
  if k=0 then (ContinuousLinearEquiv.refl ℝ WickSpaceSlice).prodCongr
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv
  else (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ WickSpaceSlice)

def wickPhysicalEuclideanPureKernel (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (k j : Fin 4) (τ : ℝ) : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (wickPureReflection k)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (momentumEuclidean.symm.prodCongr momentumEuclidean.symm)
        (wickPhysicalPurePairKernel a n u v k j τ))

end AASCKleinGordon
