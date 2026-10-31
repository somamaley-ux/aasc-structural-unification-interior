import KGWickOriginalSectorBilocalAttachment

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wickLocalMatrix_test_integrable (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : Continuous ω)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x * wickLocalMatrix a n ω G x) := by
  apply (h.integrable.norm.mul_const (∫ z, ‖G z‖ ∂particleMeasure a n)).mono'
    ((h.continuous.mul (wickLocalMatrix_continuous a n ω hω G)).aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change ‖h x * wickLocalMatrix a n ω G x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (wickLocalMatrix_uniform_bound a n ω G x) (norm_nonneg _)

theorem wickBilocalMatrix_right_test_integrable (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (k : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    Integrable (fun y => k y * wickBilocalMatrix a n ω₀ ω₁ G x y) := by
  simp_rw [wickBilocalMatrix_swap a n ω₀ ω₁ h₀ h₁ G x]
  exact wickLocalMatrix_test_integrable a n ω₁ h₁.1.continuous
    (wickPhaseStateKernel n ω₀ G x) k

theorem wickBilocalMatrix_nested_test_integrable (a : Parameters) (n : ℕ)
    (ω₀ ω₁ : ParticleConfiguration n → Spacetime)
    (h₀ : ω₀.HasTemperateGrowth) (h₁ : ω₁.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (h k : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x * ∫ y, k y * wickBilocalMatrix a n ω₀ ω₁ G x y) := by
  simp_rw [wickBilocalMatrix_smear_right a n ω₀ ω₁ h₀ h₁ G k]
  exact wickLocalMatrix_test_integrable a n ω₀ h₀.1.continuous
    (wickFourierTestStateKernel n ω₁ G k) h

theorem wick_finite_bilocal_test_sum {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (F : ι → Spacetime → Spacetime → ℂ) (h k : 𝓢(Spacetime,ℂ))
    (right_integrable : ∀ i∈S,∀ x,Integrable (fun y => k y * F i x y))
    (left_integrable : ∀ i∈S,Integrable (fun x => h x * ∫ y,k y * F i x y)) :
    (∫ x, h x * ∫ y,k y * ∑ i∈S,c i * F i x y) =
      ∑ i∈S,c i * ∫ x,h x * ∫ y,k y * F i x y := by
  classical
  have hr (x : Spacetime) : (∫ y,k y * ∑ i∈S,c i * F i x y) =
      ∑ i∈S,c i * ∫ y,k y * F i x y := by
    have hp (y : Spacetime) : k y * ∑ i∈S,c i * F i x y =
        ∑ i∈S,c i * (k y * F i x y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp_rw [hp]
    rw [integral_finset_sum _ (fun i hi => (right_integrable i hi x).const_mul (c i))]
    simp_rw [integral_const_mul]
  simp_rw [hr]
  have hp (x : Spacetime) : h x * ∑ i∈S,c i * ∫ y,k y * F i x y =
      ∑ i∈S,c i * (h x * ∫ y,k y * F i x y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hp]
  rw [integral_finset_sum _ (fun i hi => (left_integrable i hi).const_mul (c i))]
  simp_rw [integral_const_mul]

end AASCKleinGordon
