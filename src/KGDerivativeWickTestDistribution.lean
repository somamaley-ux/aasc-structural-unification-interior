import KGDerivativeWickLocalDiagonal

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

def wickCoreChannelDerivativeDistribution (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 : Spacetime) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (wickKernelEvaluationCLM a (n+2)
    (fun z => wickCoreChannelFrequency0 a n i z + wickCoreChannelFrequency1 a n i z)
    (((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)).1.continuous)
    (wickCoreChannelMixedKernel a n u v i d0 d1)).comp
      (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))

def originalDerivativeWickDistribution (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (s : ℂ)^2 • ∑ j∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 • wickCoreChannelDerivativeDistribution a j.1 u v j.2 d0 d1

theorem wickCoreChannelDerivativeDistribution_pairing (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    wickCoreChannelDerivativeDistribution a n u v i d0 d1 h =
      ∫ x,h x * wickCoreChannelMixedMatrix a n u v i d0 d1 x x := by
  simp_rw [wickCoreChannelMixedMatrix_diagonal]
  exact (wickLocalMatrix_test_pairing a (n+2) _
    (((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)).1.continuous) _ h).symm

theorem wickCoreChannelMixedMatrix_test_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x * wickCoreChannelMixedMatrix a n u v i d0 d1 x x) := by
  simp_rw [wickCoreChannelMixedMatrix_diagonal]
  exact wickLocalMatrix_test_integrable a (n+2) _
    (((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)).1.continuous) _ h

theorem originalDerivativeWickDistribution_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    originalDerivativeWickDistribution a s u v d0 d1 h =
      ∫ x,h x * originalDerivativeWickMatrix a s u v d0 d1 x := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  simp only [originalDerivativeWickDistribution, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul]
  change (s : ℂ)^2 * (∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
    wickCoreChannelDerivativeDistribution a j.1 u v j.2 d0 d1 h) = _
  have hp (x : Spacetime) : h x * originalDerivativeWickMatrix a s u v d0 d1 x =
      (s : ℂ)^2 * (h x * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
        wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x x) := by
    unfold originalDerivativeWickMatrix originalDerivativeWickBilocalCore
    ring
  simp_rw [hp, integral_const_mul]
  rw [wick_finite_local_test_sum S (fun j => wickCoreChannelCoefficient j.1 j.2)
    (fun j x => wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x x) h]
  · simp_rw [wickCoreChannelDerivativeDistribution_pairing]
  · intro j hj
    exact wickCoreChannelMixedMatrix_test_integrable a j.1 u v j.2 d0 d1 h

theorem originalDerivativeWickMatrix_test_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x * originalDerivativeWickMatrix a s u v d0 d1 x) := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hi : ∀ j∈S,Integrable (fun x => wickCoreChannelCoefficient j.1 j.2 *
      (h x * wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x x)) := by
    intro j hj
    exact (wickCoreChannelMixedMatrix_test_integrable a j.1 u v j.2 d0 d1 h).const_mul _
  have hh := (integrable_finset_sum S hi).const_mul ((s : ℂ)^2)
  convert hh using 1
  funext x
  change h x * ((s : ℂ)^2 * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
    wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x x) = _
  calc
    _ = (s : ℂ)^2 * (h x * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
      wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x x) := by ring
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem originalDerivativeWickDistribution_actual_pair_diagonal (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    originalDerivativeWickDistribution a s u v d0 d1 h =
      ∫ x,h x * fderiv ℝ (fun y => fderiv ℝ
        (fun z => originalWickBilocalCore a s u v z y) x d0) x d1 := by
  rw [originalDerivativeWickDistribution_pairing]
  simp_rw [originalDerivativeWickMatrix_eq_actual_mixed_diagonal]

end AASCKleinGordon
