import KGWickLocalMatrix
import KGEventTranslationSchwartz

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def wickPhaseCoefficient (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (x : Spacetime) (z : ParticleConfiguration n) : ℂ :=
  Real.fourierChar (-inner ℝ x (ω z))

theorem wickPhaseCoefficient_temperate (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (hω : ω.HasTemperateGrowth) (x : Spacetime) :
    (wickPhaseCoefficient n ω x).HasTemperateGrowth := by
  have hi := (Function.HasTemperateGrowth.const (2*Real.pi)).mul
    ((innerSL ℝ x).hasTemperateGrowth.comp hω)
  convert (translationPhase_temperate 1 1).comp hi using 1
  funext z
  change (Real.fourierChar (-inner ℝ x (ω z)) : ℂ) =
    Translation.phase 1 1 (2*Real.pi*inner ℝ x (ω z))
  simp only [Real.fourierChar_apply, Translation.phase, one_mul, div_one]
  congr 1
  push_cast
  ring

def wickPhaseStateKernel (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x : Spacetime) : 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω x) G

@[simp] theorem wickPhaseStateKernel_apply (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (hω : ω.HasTemperateGrowth) (G : 𝓢(ParticleConfiguration n,ℂ))
    (x : Spacetime) (z : ParticleConfiguration n) :
    wickPhaseStateKernel n ω G x z = Real.fourierChar (-inner ℝ x (ω z)) • G z := by
  rw [wickPhaseStateKernel, SchwartzMap.smulLeftCLM_apply_apply
    (wickPhaseCoefficient_temperate n ω hω x)]
  rfl

def wickFourierTestStateKernel (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) : 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z => (𝓕 h) (ω z)) G

@[simp] theorem wickFourierTestStateKernel_apply (n : ℕ) (ω : ParticleConfiguration n → Spacetime)
    (hω : ω.HasTemperateGrowth) (G : 𝓢(ParticleConfiguration n,ℂ))
    (h : 𝓢(Spacetime,ℂ)) (z : ParticleConfiguration n) :
    wickFourierTestStateKernel n ω G h z = (𝓕 h) (ω z) * G z :=
  SchwartzMap.smulLeftCLM_apply_apply ((𝓕 h).hasTemperateGrowth.comp hω) G z

def wickBilocalMatrix (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime) (G : 𝓢(ParticleConfiguration n,ℂ))
    (x y : Spacetime) : ℂ :=
  wickLocalMatrix a n ω₀ (wickPhaseStateKernel n ω₁ G y) x

theorem wickBilocalMatrix_formula (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x y : Spacetime) :
    wickBilocalMatrix a n ω₀ ω₁ G x y =
      ∫ z, Real.fourierChar (-inner ℝ x (ω₀ z)) •
        (Real.fourierChar (-inner ℝ y (ω₁ z)) • G z) ∂particleMeasure a n := by
  unfold wickBilocalMatrix wickLocalMatrix
  simp_rw [wickPhaseStateKernel_apply n ω₁ h₁]

theorem wickBilocalMatrix_swap (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x y : Spacetime) :
    wickBilocalMatrix a n ω₀ ω₁ G x y = wickBilocalMatrix a n ω₁ ω₀ G y x := by
  rw [wickBilocalMatrix_formula a n ω₀ ω₁ h₁, wickBilocalMatrix_formula a n ω₁ ω₀ h₀]
  apply integral_congr_ae
  exact ae_of_all _ fun z => smul_comm _ _ _

theorem wickBilocalMatrix_diagonal (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x : Spacetime) :
    wickBilocalMatrix a n ω₀ ω₁ G x x =
      wickLocalMatrix a n (fun z => ω₀ z + ω₁ z) G x := by
  rw [wickBilocalMatrix_formula a n ω₀ ω₁ h₁]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [inner_add_right, neg_add, AddChar.map_add_eq_mul, mul_smul]

theorem wickBilocalMatrix_smear_right (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (k : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    (∫ y, k y * wickBilocalMatrix a n ω₀ ω₁ G x y) =
      wickLocalMatrix a n ω₀ (wickFourierTestStateKernel n ω₁ G k) x := by
  simp_rw [wickBilocalMatrix_swap a n ω₀ ω₁ h₀ h₁ G x]
  change (∫ y, k y * wickLocalMatrix a n ω₁ (wickPhaseStateKernel n ω₀ G x) y) = _
  rw [wickLocalMatrix_test_pairing a n ω₁ h₁.1.continuous]
  rw [wickKernelEvaluationCLM_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [wickPhaseStateKernel_apply n ω₀ h₀,
      wickFourierTestStateKernel_apply n ω₁ h₁]
    simp only [Circle.smul_def, smul_eq_mul]
    ring

theorem wickBilocalMatrix_product_test_pairing (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x, h x * ∫ y, k y * wickBilocalMatrix a n ω₀ ω₁ G x y) =
      ∫ z, (𝓕 h) (ω₀ z) * (𝓕 k) (ω₁ z) * G z ∂particleMeasure a n := by
  simp_rw [wickBilocalMatrix_smear_right a n ω₀ ω₁ h₀ h₁ G k]
  rw [wickLocalMatrix_test_pairing a n ω₀ h₀.1.continuous,
    wickKernelEvaluationCLM_apply]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [wickFourierTestStateKernel_apply n ω₁ h₁]
    ring

end AASCKleinGordon
