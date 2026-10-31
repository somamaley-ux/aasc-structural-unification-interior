import KGWickDifferentiatedTests

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wickCoreChannelMixedMatrix_differentiated_test_pairing (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 : Spacetime) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * wickCoreChannelMixedMatrix a n u v i d0 d1 x y) =
      ∫ x,wickDirectionalTestCLM d0 h x * ∫ y,wickDirectionalTestCLM d1 k y *
        wickCoreChannelMatrix a n u v i x y :=
  wickBilocalMatrix_mixed_derivative_test_pairing a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i)
    _ d0 d1 h k

theorem originalDerivativeWickBilocalCore_test_finite_sum (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * originalDerivativeWickBilocalCore a s u v d0 d1 x y) =
      (s : ℂ)^2 * ∑ j∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        wickCoreChannelCoefficient j.1 j.2 *
          ∫ x,h x * ∫ y,k y * wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x y := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hp (x y : Spacetime) : k y * originalDerivativeWickBilocalCore a s u v d0 d1 x y =
      (s : ℂ)^2 * (k y * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
        wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x y) := by
    unfold originalDerivativeWickBilocalCore
    ring
  simp_rw [hp, integral_const_mul]
  have hx (x : Spacetime) (z : ℂ) : h x * ((s : ℂ)^2*z) = (s : ℂ)^2*(h x*z) := by ring
  simp_rw [hx, integral_const_mul]
  rw [wick_finite_bilocal_test_sum S (fun j => wickCoreChannelCoefficient j.1 j.2)
    (fun j => wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1) h k]
  · intro j hj x
    exact wickBilocalMatrix_right_test_integrable a (j.1+2) _ _
      (wickCoreChannelFrequency0_temperate a j.1 j.2)
      (wickCoreChannelFrequency1_temperate a j.1 j.2) _ k x
  · intro j hj
    exact wickBilocalMatrix_nested_test_integrable a (j.1+2) _ _
      (wickCoreChannelFrequency0_temperate a j.1 j.2)
      (wickCoreChannelFrequency1_temperate a j.1 j.2) _ h k

/-- The full derivative-Wick bilocal is the two distributional derivatives
of the SAME original pair: the two minus signs cancel exactly. -/
theorem originalDerivativeWickBilocalCore_smearing_eq_originalPairForm (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * originalDerivativeWickBilocalCore a s u v d0 d1 x y) =
      originalPairForm a s (wickDirectionalTestCLM d0 h) (wickDirectionalTestCLM d1 k) u v := by
  rw [originalDerivativeWickBilocalCore_test_finite_sum]
  simp_rw [wickCoreChannelMixedMatrix_differentiated_test_pairing]
  rw [← originalWickBilocalCore_smearing_eq_originalPairForm]
  rw [originalWickBilocalCore_test_finite_expansion]
  simp_rw [wickCoreChannelMatrix_product_test_pairing]

theorem originalWickBilocalCore_mixed_derivative_smearing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * fderiv ℝ
      (fun w => fderiv ℝ (fun z => originalWickBilocalCore a s u v z w) x d0) y d1) =
      originalPairForm a s (wickDirectionalTestCLM d0 h) (wickDirectionalTestCLM d1 k) u v := by
  simp_rw [originalWickBilocalCore_mixed_fderiv]
  exact originalDerivativeWickBilocalCore_smearing_eq_originalPairForm a s u v d0 d1 h k

end AASCKleinGordon
