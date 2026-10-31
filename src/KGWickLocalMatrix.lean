import KGWickKernelDistributions
import Mathlib.MeasureTheory.Integral.Prod

/-! Pointwise weak local channel matrices from absolutely integrable state
kernels. Their test pairing is proved by absolute Fubini, rather than an
unjustified restriction of a generic distribution to the diagonal. -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def wickLocalMatrix (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (G : 𝓢(ParticleConfiguration n,ℂ))
    (x : Spacetime) : ℂ :=
  ∫ z, Real.fourierChar (-inner ℝ x (ω z)) • G z ∂particleMeasure a n

theorem wickLocalMatrix_integrable (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x : Spacetime) :
    Integrable (fun z => Real.fourierChar (-inner ℝ x (ω z)) • G z)
      (particleMeasure a n) := by
  apply G.integrable.mono
  · exact ((Real.continuous_fourierChar.comp
      ((continuous_const.inner hω).neg)).smul G.continuous).aestronglyMeasurable
  · exact ae_of_all _ fun z => (Circle.norm_smul _ _).le

theorem wickLocalMatrix_continuous (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) : Continuous (wickLocalMatrix a n ω G) := by
  apply continuous_of_dominated
  · intro x
    exact (wickLocalMatrix_integrable a n ω hω G x).1
  · intro x
    exact ae_of_all _ fun z => (Circle.norm_smul _ _).le
  · exact G.integrable.norm
  · exact ae_of_all _ fun z => by
      exact (Real.continuous_fourierChar.comp
        ((continuous_id.inner continuous_const).neg)).smul continuous_const

theorem wickLocalMatrix_uniform_bound (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (G : 𝓢(ParticleConfiguration n,ℂ))
    (x : Spacetime) : ‖wickLocalMatrix a n ω G x‖ ≤ ∫ z, ‖G z‖ ∂particleMeasure a n := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact ae_of_all _ fun z => Circle.norm_smul _ _

theorem wickLocalMatrix_test_product_integrable (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun t : Spacetime × ParticleConfiguration n =>
      h t.1 * (Real.fourierChar (-inner ℝ t.1 (ω t.2)) • G t.2))
      (volume.prod (particleMeasure a n)) := by
  apply (h.integrable.norm.mul_prod G.integrable.norm).mono'
  · exact (h.continuous.comp continuous_fst |>.mul
      ((Real.continuous_fourierChar.comp
        ((continuous_fst.inner (hω.comp continuous_snd)).neg)).smul
          (G.continuous.comp continuous_snd))).aestronglyMeasurable
  · exact ae_of_all _ fun t => by
      change ‖h t.1 * (Real.fourierChar (-inner ℝ t.1 (ω t.2)) • G t.2)‖ ≤ _
      rw [norm_mul, Circle.norm_smul]

theorem wickLocalMatrix_test_pairing (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    ∫ x, h x * wickLocalMatrix a n ω G x =
      wickKernelEvaluationCLM a n ω hω G (𝓕 h) := by
  let I (t : Spacetime × ParticleConfiguration n) :=
    h t.1 * (Real.fourierChar (-inner ℝ t.1 (ω t.2)) • G t.2)
  have hi : Integrable I (volume.prod (particleMeasure a n)) :=
    wickLocalMatrix_test_product_integrable a n ω hω G h
  calc
    _ = ∫ x, ∫ z, I (x,z) ∂particleMeasure a n := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => (integral_const_mul _ _).symm
    _ = ∫ z, (∫ x, I (x,z)) ∂particleMeasure a n := integral_integral_swap hi
    _ = _ := by
      rw [wickKernelEvaluationCLM_apply]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        change (∫ x, h x * (Real.fourierChar (-inner ℝ x (ω z)) • G z)) =
          (𝓕 h) (ω z) * G z
        rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← integral_mul_const]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          simp only [Circle.smul_def, smul_eq_mul]
          ring

end AASCKleinGordon
