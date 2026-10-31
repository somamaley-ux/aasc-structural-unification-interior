import KGWickSchwartzTestSeparation

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem original_pair_form_symmetric (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) (u v : FiniteParticleCore) :
    originalPairForm a s h k u v=originalPairForm a s k h u v := by
  unfold originalPairForm
  rw [normalOrderedFieldPairCore_symmetric a s h k]

theorem original_wick_bilocal_smear_right_formula (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    (∫ y,k y*originalWickBilocalCore a s u v x y)=
      (s : ℂ)^2*∑ j∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        wickCoreChannelCoefficient j.1 j.2 *
          wickLocalMatrix a (j.1+2) (wickCoreChannelFrequency0 a j.1 j.2)
            (wickFourierTestStateKernel (j.1+2) (wickCoreChannelFrequency1 a j.1 j.2)
              (wickCoreChannelStateKernel j.1 u v j.2) k) x := by
  classical
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hp (y : Spacetime) : k y*originalWickBilocalCore a s u v x y=
      (s : ℂ)^2*∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
        (k y*wickCoreChannelMatrix a j.1 u v j.2 x y) := by
    change k y*((s : ℂ)^2*∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
      wickCoreChannelMatrix a j.1 u v j.2 x y)=_
    rw [show k y*((s : ℂ)^2*∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
      wickCoreChannelMatrix a j.1 u v j.2 x y)=
      (s : ℂ)^2*(k y*∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
        wickCoreChannelMatrix a j.1 u v j.2 x y) by ring]
    apply congrArg ((s : ℂ)^2 * ·)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hp]
  rw [integral_const_mul,integral_finset_sum]
  · simp_rw [integral_const_mul]
    apply congrArg ((s : ℂ)^2 * ·)
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (wickCoreChannelCoefficient j.1 j.2 * ·)
      (wickBilocalMatrix_smear_right a (j.1+2) _ _
        (wickCoreChannelFrequency0_temperate a j.1 j.2)
        (wickCoreChannelFrequency1_temperate a j.1 j.2) _ k x)
  · intro j hj
    exact (wickBilocalMatrix_right_test_integrable a (j.1+2) _ _
      (wickCoreChannelFrequency0_temperate a j.1 j.2)
      (wickCoreChannelFrequency1_temperate a j.1 j.2) _ k x).const_mul _

theorem original_wick_bilocal_smear_right_continuous (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : 𝓢(Spacetime,ℂ)) :
    Continuous (fun x => ∫ y,k y*originalWickBilocalCore a s u v x y) := by
  simp_rw [original_wick_bilocal_smear_right_formula]
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro j hj
  exact continuous_const.mul (wickLocalMatrix_smooth a (j.1+2) _
    (wickCoreChannelFrequency0_temperate a j.1 j.2) _).continuous

/-- Adjointness on the actual pointwise original pair, obtained by two
continuous Schwartz-test separations. Pair symmetry keeps the variable order
fixed, so no unproved double-integral exchange is used. -/
theorem originalWickBilocalCore_hermitian (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x y : Spacetime) :
    star (originalWickBilocalCore a s u v x y)=originalWickBilocalCore a s v u x y := by
  have hfun : (fun x y => star (originalWickBilocalCore a s u v x y))=
      originalWickBilocalCore a s v u := by
    apply wick_bilocal_eq_of_product_schwartz_tests
    · intro x
      exact (originalWickBilocalCore_right_smooth a s u v x).continuous.star
    · intro x
      exact (originalWickBilocalCore_right_smooth a s v u x).continuous
    · intro k
      have heq : (fun x => ∫ y,k y*star (originalWickBilocalCore a s u v x y))=
          fun x => star (∫ y,conjugateSchwartzCLM k y*originalWickBilocalCore a s u v x y) :=
        funext (fun x => wick_conjugate_test_integral _ k)
      rw [heq]
      exact (original_wick_bilocal_smear_right_continuous a s u v (conjugateSchwartzCLM k)).star
    · exact original_wick_bilocal_smear_right_continuous a s v u
    · intro h k
      simp_rw [wick_conjugate_test_integral]
      rw [originalWickBilocalCore_smearing_eq_originalPairForm,original_pair_form_conjugate_adjoint]
      simp only [conjugateSchwartz_involutive]
      rw [original_pair_form_symmetric]
      exact (originalWickBilocalCore_smearing_eq_originalPairForm a s v u h k).symm
  exact congrFun (congrFun hfun x) y

end AASCKleinGordon
