import KGOriginalWickMixedDerivative
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def wickDirectionalTestCLM (d : Spacetime) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  (SchwartzMap.evalCLM ℂ Spacetime ℂ d).comp (SchwartzMap.fderivCLM ℂ Spacetime ℂ)

theorem wickDirectionalTestCLM_apply (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    wickDirectionalTestCLM d h x = fderiv ℝ h x d := rfl

theorem wickDirectionalTestCLM_fourier (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) (p : Spacetime) :
    (𝓕 (wickDirectionalTestCLM d h)) p =
      (2 * Real.pi * Complex.I) * (inner ℝ p d : ℂ) * (𝓕 h) p := by
  change (𝓕 (LineDeriv.lineDerivOp d h)) p = _
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have ht : (fun p : Spacetime => inner ℝ p d).HasTemperateGrowth :=
    ((innerSL ℝ).flip d).hasTemperateGrowth
  simp only [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    Complex.real_smul, smul_eq_mul]
  ring

/-- One differentiated field factor contributes the distributional minus sign. -/
theorem wickBilocalMatrix_left_derivative_test_pairing (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (d : Spacetime) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y *
      wickBilocalMatrix a n ω0 ω1 (wickDirectionalStateKernel n ω0 d G) x y) =
      -(∫ x,wickDirectionalTestCLM d h x * ∫ y,k y * wickBilocalMatrix a n ω0 ω1 G x y) := by
  rw [wickBilocalMatrix_product_test_pairing a n ω0 ω1 h0 h1,
    wickBilocalMatrix_product_test_pairing a n ω0 ω1 h0 h1]
  rw [← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [wickDirectionalStateKernel_apply n ω0 h0, wickDirectionalTestCLM_fourier]
    unfold wickDirectionalCoefficient
    rw [real_inner_comm d (ω0 z)]
    ring

/-- The two distributional minus signs cancel, with the exact original Fourier
normalization. This does not differentiate the diagonal square. -/
theorem wickBilocalMatrix_mixed_derivative_test_pairing (a : Parameters) (n : ℕ)
    (ω0 ω1 : ParticleConfiguration n → Spacetime)
    (h0 : ω0.HasTemperateGrowth) (h1 : ω1.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (d0 d1 : Spacetime) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * wickBilocalMatrix a n ω0 ω1
      (wickDirectionalStateKernel n ω1 d1 (wickDirectionalStateKernel n ω0 d0 G)) x y) =
      ∫ x,wickDirectionalTestCLM d0 h x * ∫ y,wickDirectionalTestCLM d1 k y *
        wickBilocalMatrix a n ω0 ω1 G x y := by
  rw [wickBilocalMatrix_product_test_pairing a n ω0 ω1 h0 h1,
    wickBilocalMatrix_product_test_pairing a n ω0 ω1 h0 h1]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [wickDirectionalStateKernel_apply n ω1 h1, wickDirectionalStateKernel_apply n ω0 h0,
      wickDirectionalTestCLM_fourier, wickDirectionalTestCLM_fourier]
    unfold wickDirectionalCoefficient
    rw [real_inner_comm d0 (ω0 z), real_inner_comm d1 (ω1 z)]
    ring

end AASCKleinGordon
