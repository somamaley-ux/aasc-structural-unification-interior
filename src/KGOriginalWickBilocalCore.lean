import KGWickBilocalIntegrability
import KGWickCreationPairChannel
import KGOriginalPairKernelAssembly

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

/-- Channel order: CC, CA, reversed CA, AA, matching the proved original pair. -/
def wickCoreChannelFrequency0 (a : Parameters) (n : ℕ) (i : Fin 4) :
    ParticleConfiguration (n+2) → Spacetime :=
  ![wickShellFrequencyAt a n 0, wickShellFrequencyAt a n 0,
    -wickShellFrequencyAt a n 1, -wickShellFrequencyAt a n 1] i

def wickCoreChannelFrequency1 (a : Parameters) (n : ℕ) (i : Fin 4) :
    ParticleConfiguration (n+2) → Spacetime :=
  ![wickShellFrequencyAt a n 1, -wickShellFrequencyAt a n 1,
    wickShellFrequencyAt a n 0, -wickShellFrequencyAt a n 0] i

theorem wickCoreChannelFrequency0_temperate (a : Parameters) (n : ℕ) (i : Fin 4) :
    (wickCoreChannelFrequency0 a n i).HasTemperateGrowth := by
  fin_cases i <;> dsimp [wickCoreChannelFrequency0]
  · exact wickShellFrequencyAt_temperate a n 0
  · exact wickShellFrequencyAt_temperate a n 0
  · exact (wickShellFrequencyAt_temperate a n 1).neg
  · exact (wickShellFrequencyAt_temperate a n 1).neg

theorem wickCoreChannelFrequency1_temperate (a : Parameters) (n : ℕ) (i : Fin 4) :
    (wickCoreChannelFrequency1 a n i).HasTemperateGrowth := by
  fin_cases i <;> dsimp [wickCoreChannelFrequency1]
  · exact wickShellFrequencyAt_temperate a n 1
  · exact (wickShellFrequencyAt_temperate a n 1).neg
  · exact wickShellFrequencyAt_temperate a n 0
  · exact (wickShellFrequencyAt_temperate a n 0).neg

def wickCoreChannelStateKernel (n : ℕ) (u v : FiniteParticleCore) (i : Fin 4) :
    𝓢(ParticleConfiguration (n+2),ℂ) :=
  ![conjugateSchwartzCLM (wickAAStateKernel n (v n).val (u (n+2)).val),
    wickMixedStateKernel n (u (n+1)).val (v (n+1)).val,
    wickMixedStateKernel n (u (n+1)).val (v (n+1)).val,
    wickAAStateKernel n (u n).val (v (n+2)).val] i

def wickCoreChannelCoefficient (n : ℕ) (i : Fin 4) : ℂ :=
  ![(Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ), ((n+1 : ℝ) : ℂ),
    ((n+1 : ℝ) : ℂ), (Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ)] i

def wickCoreChannelMatrix (a : Parameters) (n : ℕ) (u v : FiniteParticleCore) (i : Fin 4)
    (x y : Spacetime) : ℂ :=
  wickBilocalMatrix a (n+2) (wickCoreChannelFrequency0 a n i)
    (wickCoreChannelFrequency1 a n i) (wickCoreChannelStateKernel n u v i) x y

theorem wickCoreChannelMatrix_product_test_pairing (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * wickCoreChannelMatrix a n u v i x y) =
      ∫ z,(𝓕 h) (wickCoreChannelFrequency0 a n i z) *
        (𝓕 k) (wickCoreChannelFrequency1 a n i z) * wickCoreChannelStateKernel n u v i z
          ∂particleMeasure a (n+2) :=
  wickBilocalMatrix_product_test_pairing a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ h k

def originalWickBilocalCore (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (x y : Spacetime) : ℂ :=
  (s : ℂ)^2 * ∑ j ∈ (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 * wickCoreChannelMatrix a j.1 u v j.2 x y

theorem originalWickBilocalCore_test_finite_expansion (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * originalWickBilocalCore a s u v x y) =
      (s : ℂ)^2 * ∑ j ∈ (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
        wickCoreChannelCoefficient j.1 j.2 *
          ∫ z,(𝓕 h) (wickCoreChannelFrequency0 a j.1 j.2 z) *
            (𝓕 k) (wickCoreChannelFrequency1 a j.1 j.2 z) *
              wickCoreChannelStateKernel j.1 u v j.2 z ∂particleMeasure a (j.1+2) := by
  let S := (Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4))
  have hp (x y : Spacetime) : k y * originalWickBilocalCore a s u v x y =
      (s : ℂ)^2 * (k y * ∑ j∈S,wickCoreChannelCoefficient j.1 j.2 *
        wickCoreChannelMatrix a j.1 u v j.2 x y) := by unfold originalWickBilocalCore; ring
  simp_rw [hp, integral_const_mul]
  have hx (x : Spacetime) (z : ℂ) : h x * ((s : ℂ)^2*z) = (s : ℂ)^2*(h x*z) := by ring
  simp_rw [hx, integral_const_mul]
  rw [wick_finite_bilocal_test_sum S
    (fun j => wickCoreChannelCoefficient j.1 j.2)
    (fun j => wickCoreChannelMatrix a j.1 u v j.2) h k]
  · simp_rw [wickCoreChannelMatrix_product_test_pairing]
    rfl
  · intro j hj x
    exact wickBilocalMatrix_right_test_integrable a (j.1+2) _ _
      (wickCoreChannelFrequency0_temperate a j.1 j.2)
      (wickCoreChannelFrequency1_temperate a j.1 j.2) _ k x
  · intro j hj
    exact wickBilocalMatrix_nested_test_integrable a (j.1+2) _ _
      (wickCoreChannelFrequency0_temperate a j.1 j.2)
      (wickCoreChannelFrequency1_temperate a j.1 j.2) _ h k

end AASCKleinGordon
