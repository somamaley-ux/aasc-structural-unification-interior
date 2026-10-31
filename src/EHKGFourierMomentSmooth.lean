import EHKGFullFlatCauchy
import KGSpacetimeEuclideanSplit
import KGNormalizedShellTimeIntegrals
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Volume-measure specialization of the retained Wick graph-Fourier argument.
All frequency moments are proved integrable from actual Schwartz amplitudes.
The resulting full spacetime C-infinity theorem assumes no PDE evolution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

theorem volume_frequency_moments_integrable (k : ℕ)
    (sigma : KGSpatialSpace → Spacetime) (growth : sigma.HasTemperateGrowth)
    (G : 𝓢(KGSpatialSpace, ℂ)) :
    Integrable (fun z => ‖sigma z‖ ^ k * ‖G z‖) := by
  let weight (z : KGSpatialSpace) : ℝ := (1 + ‖sigma z‖ ^ 2) ^ k
  have hw : weight.HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const 1).add
      ((Function.hasTemperateGrowth_norm_sq Spacetime).comp growth)).pow k
  have hwC : (fun z => (weight z : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp hw
  let H := SchwartzMap.smulLeftCLM ℂ (fun z => (weight z : ℂ)) G
  have normH (z) : ‖H z‖ = weight z * ‖G z‖ := by
    dsimp [H]
    rw [SchwartzMap.smulLeftCLM_apply_apply hwC, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by dsimp [weight]; positivity)]
  have integrableWeight : Integrable (fun z => weight z * ‖G z‖) := by
    simpa only [normH] using H.integrable.norm
  apply integrableWeight.mono'
    (((growth.1.continuous.norm.pow k).mul G.continuous.norm).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖‖sigma z‖ ^ k * ‖G z‖‖ ≤ weight z * ‖G z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    dsimp [weight]
    nlinarith [sq_nonneg (‖sigma z‖ - 1)]

def volumeFrequencyGraph (sigma : KGSpatialSpace → Spacetime) (z : KGSpatialSpace) :
    Spacetime × KGSpatialSpace := (sigma z, z)

theorem volume_graph_moments_integrable (k : ℕ)
    (sigma : KGSpatialSpace → Spacetime) (growth : sigma.HasTemperateGrowth)
    (G : 𝓢(KGSpatialSpace, ℂ)) :
    Integrable (fun z => ‖volumeFrequencyGraph sigma z‖ ^ k * ‖G z‖) := by
  have bound := (volume_frequency_moments_integrable k sigma growth G).add
    (G.integrable_pow_mul volume k)
  have continuousGraph : Continuous (volumeFrequencyGraph sigma) := growth.1.continuous.prodMk continuous_id
  apply bound.mono' (((continuousGraph.norm.pow k).mul G.continuous.norm).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖‖volumeFrequencyGraph sigma z‖ ^ k * ‖G z‖‖ ≤
      ‖sigma z‖ ^ k * ‖G z‖ + ‖z‖ ^ k * ‖G z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← add_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change (max ‖sigma z‖ ‖z‖) ^ k ≤ ‖sigma z‖ ^ k + ‖z‖ ^ k
    rcases le_total ‖sigma z‖ ‖z‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)

def volumeGraphPairing :
    (Spacetime × KGSpatialSpace) →L[ℝ] Spacetime →L[ℝ] ℝ :=
  (innerSL ℝ : Spacetime →L[ℝ] Spacetime →L[ℝ] ℝ).comp
    (ContinuousLinearMap.fst ℝ Spacetime KGSpatialSpace)

def volumePhaseIntegral (sigma : KGSpatialSpace → Spacetime) (G : 𝓢(KGSpatialSpace, ℂ))
    (x : Spacetime) : ℂ := ∫ z, Real.fourierChar (-inner ℝ x (sigma z)) • G z

theorem volume_phase_eq_graph_fourier (sigma : KGSpatialSpace → Spacetime)
    (continuousSigma : Continuous sigma) (G : 𝓢(KGSpatialSpace, ℂ)) :
    volumePhaseIntegral sigma G =
      VectorFourier.fourierIntegral Real.fourierChar
        (Measure.map (volumeFrequencyGraph sigma) volume)
        volumeGraphPairing.toLinearMap₁₂
        (fun z : Spacetime × KGSpatialSpace => G z.2) := by
  funext x
  have continuousGraph : Continuous (volumeFrequencyGraph sigma) := continuousSigma.prodMk continuous_id
  rw [VectorFourier.fourierIntegral, integral_map continuousGraph.aemeasurable]
  · apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change Real.fourierChar (-inner ℝ x (sigma z)) • G z =
        Real.fourierChar (-inner ℝ (sigma z) x) • G z
      rw [real_inner_comm x (sigma z)]
  · exact ((Real.continuous_fourierChar.comp
      ((volumeGraphPairing.flip x).continuous.neg)).smul
        (G.continuous.comp continuous_snd)).aestronglyMeasurable

theorem volume_phase_smooth (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (G : 𝓢(KGSpatialSpace, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (volumePhaseIntegral sigma G) := by
  rw [volume_phase_eq_graph_fourier sigma growth.1.continuous G]
  apply VectorFourier.contDiff_fourierIntegral volumeGraphPairing
  intro k hk
  apply (integrable_map_measure
    ((((continuous_norm.pow k).mul (G.continuous.comp continuous_snd).norm)).aestronglyMeasurable)
    ((growth.1.continuous.prodMk continuous_id).aemeasurable)).mpr
  exact volume_graph_moments_integrable k sigma growth G

def spatialEventInjection : KGSpatialSpace →L[ℝ] Spacetime :=
  spatialInjection.comp momentumEuclidean.symm.toContinuousLinearMap

def homogeneousPhaseFrequency (a : Parameters) (sign : ℝ) (xi : KGSpatialSpace) : Spacetime :=
  timeInjection (-(sign / (2 * Real.pi)) * spatialOmega a xi) - spatialEventInjection xi

theorem homogeneous_phase_frequency_temperate (a : Parameters) (sign : ℝ) :
    (homogeneousPhaseFrequency a sign).HasTemperateGrowth :=
  (timeInjection.hasTemperateGrowth.comp
    ((Function.HasTemperateGrowth.const (-(sign / (2 * Real.pi)))).mul
      (spatialOmega_temperate a))).sub spatialEventInjection.hasTemperateGrowth

theorem homogeneous_phase_smooth (a : Parameters) (sign : ℝ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (volumePhaseIntegral (homogeneousPhaseFrequency a sign) G) :=
  volume_phase_smooth _ (homogeneous_phase_frequency_temperate a sign) G

end AASCKleinGordon.CurvedKG
