import KGWickStateKernels
import KGSpacetimeSmearing

/-! Concrete local-channel tempered functionals from the original entangled
state coefficients. The shell-sum/difference evaluation is only bounded
evaluation against an integrable state coefficient, never a Schwartz pullback
along the nonproper mixed shell-difference map. Full original-core bilocal
smearing identification and derivative-Wick EMT assembly are later steps. -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem wickKernelTest_integrable (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun z => h (ω z) * G z) (particleMeasure a n) := by
  apply (G.integrable.norm.const_mul (SchwartzMap.seminorm ℂ 0 0 h)).mono'
    (((h.continuous.comp hω).mul G.continuous).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    change ‖h (ω z) * G z‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ h (ω z))
      (norm_nonneg _)

theorem wickKernelTest_bound (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    ‖∫ z, h (ω z) * G z ∂particleMeasure a n‖ ≤
      (∫ z, ‖G z‖ ∂particleMeasure a n) * SchwartzMap.seminorm ℂ 0 0 h := by
  calc
    _ ≤ ∫ z, ‖h (ω z) * G z‖ ∂particleMeasure a n := norm_integral_le_integral_norm _
    _ ≤ ∫ z, SchwartzMap.seminorm ℂ 0 0 h * ‖G z‖ ∂particleMeasure a n := by
      apply integral_mono (wickKernelTest_integrable a n ω hω G h).norm
        (G.integrable.norm.const_mul _)
      intro z
      change ‖h (ω z) * G z‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ h (ω z))
        (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

def wickKernelEvaluationCLM (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ := by
  refine SchwartzMap.mkCLMtoNormedSpace (fun h => ∫ z, h (ω z) * G z ∂particleMeasure a n)
    (fun h k => ?_) (fun c h => ?_) ?_
  · simp only [SchwartzMap.add_apply, add_mul]
    exact integral_add (wickKernelTest_integrable a n ω hω G h)
      (wickKernelTest_integrable a n ω hω G k)
  · simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul _ _
  · refine ⟨{(0,0)}, ∫ z, ‖G z‖ ∂particleMeasure a n, integral_nonneg (fun z => norm_nonneg _), ?_⟩
    intro h
    simpa using wickKernelTest_bound a n ω hω G h

@[simp] theorem wickKernelEvaluationCLM_apply (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickKernelEvaluationCLM a n ω hω G h = ∫ z, h (ω z) * G z ∂particleMeasure a n := rfl

def wickAAShellFrequency (a : Parameters) (n : ℕ) (z : ParticleConfiguration (n+2)) :
    Spacetime := -(shellFrequency a (z 0) + shellFrequency a (z 1))

def wickMixedShellFrequency (a : Parameters) (n : ℕ) (z : ParticleConfiguration (n+2)) :
    Spacetime := shellFrequency a (z 0) - shellFrequency a (z 1)

theorem wickAAShellFrequency_continuous (a : Parameters) (n : ℕ) :
    Continuous (wickAAShellFrequency a n) :=
  (((shellFrequency_temperate a).1.continuous.comp (continuous_apply 0)).add
    ((shellFrequency_temperate a).1.continuous.comp (continuous_apply 1))).neg

theorem wickMixedShellFrequency_continuous (a : Parameters) (n : ℕ) :
    Continuous (wickMixedShellFrequency a n) :=
  ((shellFrequency_temperate a).1.continuous.comp (continuous_apply 0)).sub
    ((shellFrequency_temperate a).1.continuous.comp (continuous_apply 1))

def wickAALocalSectorDistribution (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (wickKernelEvaluationCLM a (n+2) (wickAAShellFrequency a n)
    (wickAAShellFrequency_continuous a n) (wickAAStateKernel n u v)).comp
      (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))

def wickMixedLocalSectorDistribution (a : Parameters) (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (wickKernelEvaluationCLM a (n+2) (wickMixedShellFrequency a n)
    (wickMixedShellFrequency_continuous a n) (wickMixedStateKernel n u v)).comp
      (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))

theorem wickAALocalSectorDistribution_formula (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ))
    (h : 𝓢(Spacetime,ℂ)) :
    wickAALocalSectorDistribution a n u v h =
      ∫ z, (𝓕 h) (-(shellFrequency a (z 0) + shellFrequency a (z 1))) *
        (star (u (Fin.tail (Fin.tail z))) * v z) ∂particleMeasure a (n+2) := rfl

theorem wickMixedLocalSectorDistribution_formula (a : Parameters) (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    wickMixedLocalSectorDistribution a n u v h =
      ∫ z, (𝓕 h) (shellFrequency a (z 0) - shellFrequency a (z 1)) *
        (star (u (Fin.cons (z 0) (Fin.tail (Fin.tail z)))) * v (Fin.tail z))
          ∂particleMeasure a (n+2) := rfl

end AASCKleinGordon
