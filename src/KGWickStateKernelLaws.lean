import KGOriginalWickBilocalCore

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wickCoreChannelStateKernel_add_left (n : ℕ) (u u' v : FiniteParticleCore) (i : Fin 4) :
    wickCoreChannelStateKernel n (u+u') v i =
      wickCoreChannelStateKernel n u v i + wickCoreChannelStateKernel n u' v i := by
  apply SchwartzMap.ext
  intro z
  fin_cases i <;> simp [wickCoreChannelStateKernel, wickAAStateKernel_apply,
    wickMixedStateKernel_apply, DirectSum.add_apply, add_mul, mul_add]

theorem wickCoreChannelStateKernel_add_right (n : ℕ) (u v v' : FiniteParticleCore) (i : Fin 4) :
    wickCoreChannelStateKernel n u (v+v') i =
      wickCoreChannelStateKernel n u v i + wickCoreChannelStateKernel n u v' i := by
  apply SchwartzMap.ext
  intro z
  fin_cases i <;> simp [wickCoreChannelStateKernel, wickAAStateKernel_apply,
    wickMixedStateKernel_apply, DirectSum.add_apply, add_mul, mul_add]

theorem wickCoreChannelStateKernel_smul_left (n : ℕ) (c : ℂ) (u v : FiniteParticleCore) (i : Fin 4) :
    wickCoreChannelStateKernel n (c • u) v i = star c • wickCoreChannelStateKernel n u v i := by
  apply SchwartzMap.ext
  intro z
  fin_cases i <;> simp [wickCoreChannelStateKernel, wickAAStateKernel_apply,
    wickMixedStateKernel_apply, DirectSum.smul_apply, star_mul, mul_comm, mul_left_comm, mul_assoc]

theorem wickCoreChannelStateKernel_smul_right (n : ℕ) (c : ℂ) (u v : FiniteParticleCore) (i : Fin 4) :
    wickCoreChannelStateKernel n u (c • v) i = c • wickCoreChannelStateKernel n u v i := by
  apply SchwartzMap.ext
  intro z
  fin_cases i <;> simp [wickCoreChannelStateKernel, wickAAStateKernel_apply,
    wickMixedStateKernel_apply, DirectSum.smul_apply, star_mul, mul_comm, mul_left_comm, mul_assoc]

def wickBilocalKernelFunctional (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime) (x y : Spacetime) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (particleMeasure a n)).comp
    ((SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω₀ x)).comp
      (SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω₁ y)))

theorem wickBilocalKernelFunctional_apply (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x y : Spacetime) :
    wickBilocalKernelFunctional a n ω₀ ω₁ x y G = wickBilocalMatrix a n ω₀ ω₁ G x y := by
  rw [wickBilocalMatrix_formula a n ω₀ ω₁ h₁]
  change (∫ z, (SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω₀ x)
    (SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω₁ y) G)) z ∂particleMeasure a n) = _
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (wickPhaseCoefficient_temperate n ω₀ h₀ x),
      SchwartzMap.smulLeftCLM_apply_apply (wickPhaseCoefficient_temperate n ω₁ h₁ y)]
    rfl

theorem wickBilocalMatrix_add_kernel (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G H : 𝓢(ParticleConfiguration n,ℂ)) (x y : Spacetime) :
    wickBilocalMatrix a n ω₀ ω₁ (G+H) x y =
      wickBilocalMatrix a n ω₀ ω₁ G x y + wickBilocalMatrix a n ω₀ ω₁ H x y := by
  rw [← wickBilocalKernelFunctional_apply a n ω₀ ω₁ h₀ h₁ (G+H), map_add,
    wickBilocalKernelFunctional_apply a n ω₀ ω₁ h₀ h₁ G,
    wickBilocalKernelFunctional_apply a n ω₀ ω₁ h₀ h₁ H]

theorem wickBilocalMatrix_smul_kernel (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (c : ℂ) (G : 𝓢(ParticleConfiguration n,ℂ)) (x y : Spacetime) :
    wickBilocalMatrix a n ω₀ ω₁ (c • G) x y = c * wickBilocalMatrix a n ω₀ ω₁ G x y := by
  rw [← wickBilocalKernelFunctional_apply a n ω₀ ω₁ h₀ h₁ (c • G), map_smul,
    wickBilocalKernelFunctional_apply a n ω₀ ω₁ h₀ h₁ G]
  rfl

end AASCKleinGordon
