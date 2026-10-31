import KGWickFiniteDerivativeExchange

noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

def wickCoreChannelFirstKernel (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (i : Fin 4) (d0 : Spacetime) : 𝓢(ParticleConfiguration (n+2),ℂ) :=
  wickDirectionalStateKernel (n+2) (wickCoreChannelFrequency0 a n i) d0
    (wickCoreChannelStateKernel n u v i)

def wickCoreChannelMixedKernel (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (i : Fin 4) (d0 d1 : Spacetime) : 𝓢(ParticleConfiguration (n+2),ℂ) :=
  wickDirectionalStateKernel (n+2) (wickCoreChannelFrequency1 a n i) d1
    (wickCoreChannelFirstKernel a n u v i d0)

def wickCoreChannelFirstMatrix (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (i : Fin 4) (d0 x y : Spacetime) : ℂ :=
  wickBilocalMatrix a (n+2) (wickCoreChannelFrequency0 a n i)
    (wickCoreChannelFrequency1 a n i) (wickCoreChannelFirstKernel a n u v i d0) x y

def wickCoreChannelMixedMatrix (a : Parameters) (n : ℕ) (u v : FiniteParticleCore)
    (i : Fin 4) (d0 d1 x y : Spacetime) : ℂ :=
  wickBilocalMatrix a (n+2) (wickCoreChannelFrequency0 a n i)
    (wickCoreChannelFrequency1 a n i) (wickCoreChannelMixedKernel a n u v i d0 d1) x y

theorem wickCoreChannelMatrix_fderiv_left (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (x y d0 : Spacetime) :
    fderiv ℝ (fun x => wickCoreChannelMatrix a n u v i x y) x d0 =
      wickCoreChannelFirstMatrix a n u v i d0 x y :=
  wickBilocalMatrix_fderiv_left a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ x y d0

theorem wickCoreChannelFirstMatrix_right_smooth (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 x : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => wickCoreChannelFirstMatrix a n u v i d0 x y) := by
  unfold wickCoreChannelFirstMatrix
  simp_rw [wickBilocalMatrix_swap a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i)]
  exact wickLocalMatrix_smooth a (n+2) _ (wickCoreChannelFrequency1_temperate a n i) _

theorem wickCoreChannelFirstMatrix_fderiv_right (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (x y d0 d1 : Spacetime) :
    fderiv ℝ (fun y => wickCoreChannelFirstMatrix a n u v i d0 x y) y d1 =
      wickCoreChannelMixedMatrix a n u v i d0 d1 x y :=
  wickBilocalMatrix_fderiv_right a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ x y d1

def originalFirstDerivativeWickBilocalCore (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 x y : Spacetime) : ℂ :=
  (s : ℂ)^2 * ∑ j∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 * wickCoreChannelFirstMatrix a j.1 u v j.2 d0 x y

def originalDerivativeWickBilocalCore (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 x y : Spacetime) : ℂ :=
  (s : ℂ)^2 * ∑ j∈(Finset.range (wickJointCoreCutoff u v)).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 * wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x y

theorem originalWickBilocalCore_fderiv_left (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x y d0 : Spacetime) :
    fderiv ℝ (fun x => originalWickBilocalCore a s u v x y) x d0 =
      originalFirstDerivativeWickBilocalCore a s u v d0 x y := by
  unfold originalWickBilocalCore originalFirstDerivativeWickBilocalCore
  rw [wick_scaled_finite_weighted_directional_derivative]
  · simp_rw [wickCoreChannelMatrix_fderiv_left]
  · intro j hj
    exact (wickCoreChannelMatrix_left_smooth a j.1 u v j.2 y).differentiable (by simp) x

/-- The actual mixed derivative of the complete original normal-ordered pair
matrix. Derivative exchange with the full finite channel sum is proved. -/
theorem originalWickBilocalCore_mixed_fderiv (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x y d0 d1 : Spacetime) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => originalWickBilocalCore a s u v z y) x d0) y d1 =
      originalDerivativeWickBilocalCore a s u v d0 d1 x y := by
  simp_rw [originalWickBilocalCore_fderiv_left]
  unfold originalFirstDerivativeWickBilocalCore originalDerivativeWickBilocalCore
  rw [wick_scaled_finite_weighted_directional_derivative]
  · simp_rw [wickCoreChannelFirstMatrix_fderiv_right]
  · intro j hj
    exact (wickCoreChannelFirstMatrix_right_smooth a j.1 u v j.2 d0 x).differentiable (by simp) y

theorem wickCoreChannelMixedKernel_apply (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 : Spacetime)
    (z : ParticleConfiguration (n+2)) :
    wickCoreChannelMixedKernel a n u v i d0 d1 z =
      wickDirectionalCoefficient (n+2) (wickCoreChannelFrequency1 a n i) d1 z *
      (wickDirectionalCoefficient (n+2) (wickCoreChannelFrequency0 a n i) d0 z *
        wickCoreChannelStateKernel n u v i z) := by
  unfold wickCoreChannelMixedKernel wickCoreChannelFirstKernel
  rw [wickDirectionalStateKernel_apply _ _ (wickCoreChannelFrequency1_temperate a n i),
    wickDirectionalStateKernel_apply _ _ (wickCoreChannelFrequency0_temperate a n i)]

end AASCKleinGordon
