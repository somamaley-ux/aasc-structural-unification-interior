import KGOriginalWickBilocalCore

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem wickCoreChannelMatrix_diagonal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (x : Spacetime) :
    wickCoreChannelMatrix a n u v i x x =
      wickLocalMatrix a (n+2)
        (fun z => wickCoreChannelFrequency0 a n i z + wickCoreChannelFrequency1 a n i z)
        (wickCoreChannelStateKernel n u v i) x :=
  wickBilocalMatrix_diagonal a (n+2) _ _ (wickCoreChannelFrequency1_temperate a n i) _ x

theorem wickCoreChannelMatrix_diagonal_smooth (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => wickCoreChannelMatrix a n u v i x x) := by
  simp_rw [wickCoreChannelMatrix_diagonal]
  exact wickLocalMatrix_smooth a (n+2) _
    ((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)) _

def originalWickSquareMatrix (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) (x : Spacetime) : ℂ :=
  originalWickBilocalCore a s u v x x

theorem originalWickSquareMatrix_smooth (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) :
    ContDiff ℝ (⊤ : ℕ∞) (originalWickSquareMatrix a s u v) := by
  unfold originalWickSquareMatrix originalWickBilocalCore
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (wickCoreChannelMatrix_diagonal_smooth a j.1 u v j.2)

def wickCoreChannelLocalDistribution (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (wickKernelEvaluationCLM a (n+2)
    (fun z => wickCoreChannelFrequency0 a n i z + wickCoreChannelFrequency1 a n i z)
    (((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)).1.continuous)
    (wickCoreChannelStateKernel n u v i)).comp (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ))

def originalWickSquareDistribution (a : Parameters) (s : ℝ) (u v : FiniteParticleCore) :
    𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (s : ℂ)^2 • ∑ j ∈ (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 • wickCoreChannelLocalDistribution a j.1 u v j.2

theorem wick_finite_local_test_sum {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (F : ι → Spacetime → ℂ) (h : 𝓢(Spacetime,ℂ))
    (hi : ∀ i∈S,Integrable (fun x => h x * F i x)) :
    (∫ x,h x * ∑ i∈S,c i * F i x) = ∑ i∈S,c i * ∫ x,h x * F i x := by
  classical
  have hp (x : Spacetime) : h x * ∑ i∈S,c i * F i x =
      ∑ i∈S,c i * (h x * F i x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [hp]
  rw [integral_finset_sum _ (fun i his => (hi i his).const_mul (c i))]
  simp_rw [integral_const_mul]

theorem wickCoreChannelLocalDistribution_pairing (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    wickCoreChannelLocalDistribution a n u v i h =
      ∫ x,h x * wickCoreChannelMatrix a n u v i x x := by
  simp_rw [wickCoreChannelMatrix_diagonal]
  exact (wickLocalMatrix_test_pairing a (n+2) _
    (((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)).1.continuous) _ h).symm

theorem originalWickSquareDistribution_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h : 𝓢(Spacetime,ℂ)) :
    originalWickSquareDistribution a s u v h = ∫ x,h x * originalWickSquareMatrix a s u v x := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  simp only [originalWickSquareDistribution, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul]
  change (s : ℂ)^2 * (∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
    wickCoreChannelLocalDistribution a j.1 u v j.2 h) = _
  have hp (x : Spacetime) : h x * originalWickSquareMatrix a s u v x =
      (s : ℂ)^2 * (h x * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
        wickCoreChannelMatrix a j.1 u v j.2 x x) := by
    unfold originalWickSquareMatrix originalWickBilocalCore
    ring
  simp_rw [hp, integral_const_mul]
  rw [wick_finite_local_test_sum S (fun j => wickCoreChannelCoefficient j.1 j.2)
    (fun j x => wickCoreChannelMatrix a j.1 u v j.2 x x) h]
  · simp_rw [wickCoreChannelLocalDistribution_pairing]
  · intro j hj
    simp_rw [wickCoreChannelMatrix_diagonal]
    exact wickLocalMatrix_test_integrable a (j.1+2) _
      (((wickCoreChannelFrequency0_temperate a j.1 j.2).add
        (wickCoreChannelFrequency1_temperate a j.1 j.2)).1.continuous) _ h

end AASCKleinGordon
