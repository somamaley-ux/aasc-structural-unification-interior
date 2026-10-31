import KGWickLocalMatrix
import Mathlib.Analysis.Fourier.FourierTransformDeriv

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_frequency_moments_integrable (a : Parameters) (n k : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) :
    Integrable (fun z => ‖ω z‖^k * ‖G z‖) (particleMeasure a n) := by
  let ψ (z : ParticleConfiguration n) : ℝ := (1+‖ω z‖^2)^k
  have hψ : ψ.HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const 1).add
      ((Function.hasTemperateGrowth_norm_sq Spacetime).comp hω)).pow k
  have hψC : (fun z => (ψ z : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp hψ
  let H := SchwartzMap.smulLeftCLM ℂ (fun z => (ψ z : ℂ)) G
  have hn (z) : ‖H z‖ = ψ z * ‖G z‖ := by
    dsimp [H]
    rw [SchwartzMap.smulLeftCLM_apply_apply hψC, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by dsimp [ψ]; positivity)]
  have hi : Integrable (fun z => ψ z * ‖G z‖) (particleMeasure a n) := by
    simpa only [hn] using H.integrable.norm (μ:=particleMeasure a n)
  apply hi.mono'
    (((hω.1.continuous.norm.pow k).mul G.continuous.norm).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖‖ω z‖^k * ‖G z‖‖ ≤ ψ z * ‖G z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    dsimp [ψ]
    nlinarith [sq_nonneg (‖ω z‖-1)]

def wickFrequencyGraph (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (z : ParticleConfiguration n) : Spacetime × ParticleConfiguration n := (ω z,z)

theorem wick_graph_moments_integrable (a : Parameters) (n k : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) :
    Integrable (fun z => ‖wickFrequencyGraph n ω z‖^k * ‖G z‖) (particleMeasure a n) := by
  have hi := (wick_frequency_moments_integrable a n k ω hω G).add
    (G.integrable_pow_mul (particleMeasure a n) k)
  have he : Continuous (wickFrequencyGraph n ω) := hω.1.continuous.prodMk continuous_id
  apply hi.mono' (((he.norm.pow k).mul G.continuous.norm).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖‖wickFrequencyGraph n ω z‖^k * ‖G z‖‖ ≤
      ‖ω z‖^k * ‖G z‖ + ‖z‖^k * ‖G z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change (max ‖ω z‖ ‖z‖)^k ≤ ‖ω z‖^k+‖z‖^k
    rcases le_total ‖ω z‖ ‖z‖ with h|h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) _)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)

def wickGraphPairing (n : ℕ) :
    (Spacetime × ParticleConfiguration n) →L[ℝ] Spacetime →L[ℝ] ℝ :=
  (innerSL ℝ : Spacetime →L[ℝ] Spacetime →L[ℝ] ℝ).comp
    (ContinuousLinearMap.fst ℝ Spacetime (ParticleConfiguration n))

theorem wickLocalMatrix_eq_graph_fourier (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) :
    wickLocalMatrix a n ω G =
      VectorFourier.fourierIntegral Real.fourierChar
        (Measure.map (wickFrequencyGraph n ω) (particleMeasure a n))
        (wickGraphPairing n).toLinearMap₁₂
        (fun t : Spacetime × ParticleConfiguration n => G t.2) := by
  funext x
  have he : Continuous (wickFrequencyGraph n ω) := hω.prodMk continuous_id
  rw [VectorFourier.fourierIntegral]
  rw [integral_map he.aemeasurable]
  · apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change Real.fourierChar (-inner ℝ x (ω z)) • G z =
        Real.fourierChar (-inner ℝ (ω z) x) • G z
      rw [real_inner_comm x (ω z)]
  · exact ((Real.continuous_fourierChar.comp
      (((wickGraphPairing n).flip x).continuous.neg)).smul
        (G.continuous.comp continuous_snd)).aestronglyMeasurable

theorem wickLocalMatrix_smooth (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) : ContDiff ℝ (⊤ : ℕ∞) (wickLocalMatrix a n ω G) := by
  rw [wickLocalMatrix_eq_graph_fourier a n ω hω.1.continuous G]
  apply VectorFourier.contDiff_fourierIntegral (wickGraphPairing n)
  intro k hk
  apply (integrable_map_measure
    ((((continuous_norm.pow k).mul (G.continuous.comp continuous_snd).norm)).aestronglyMeasurable)
    ((hω.1.continuous.prodMk continuous_id).aemeasurable)).mpr
  exact wick_graph_moments_integrable a n k ω hω G

end AASCKleinGordon
