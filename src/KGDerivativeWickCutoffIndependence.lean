import KGDerivativeWickLocalDiagonal

noncomputable section
set_option maxHeartbeats 4000000
namespace AASCKleinGordon

def originalFirstDerivativeWickBilocalCoreAt (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ) (d0 x y : Spacetime) : ℂ :=
  (s : ℂ)^2 * ∑ j∈(Finset.range N).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 * wickCoreChannelFirstMatrix a j.1 u v j.2 d0 x y

def originalDerivativeWickBilocalCoreAt (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ) (d0 d1 x y : Spacetime) : ℂ :=
  (s : ℂ)^2 * ∑ j∈(Finset.range N).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 * wickCoreChannelMixedMatrix a j.1 u v j.2 d0 d1 x y

theorem originalWickBilocalCoreAt_fderiv_left (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ) (x y d0 : Spacetime) :
    fderiv ℝ (fun z => originalWickBilocalCoreAt a s u v N z y) x d0 =
      originalFirstDerivativeWickBilocalCoreAt a s u v N d0 x y := by
  unfold originalWickBilocalCoreAt originalFirstDerivativeWickBilocalCoreAt
  rw [wick_scaled_finite_weighted_directional_derivative]
  · simp_rw [wickCoreChannelMatrix_fderiv_left]
  · intro j hj
    exact (wickCoreChannelMatrix_left_smooth a j.1 u v j.2 y).differentiable (by simp) x

theorem originalFirstDerivativeWickBilocalCoreAt_fderiv_right (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ) (x y d0 d1 : Spacetime) :
    fderiv ℝ (fun z => originalFirstDerivativeWickBilocalCoreAt a s u v N d0 x z) y d1 =
      originalDerivativeWickBilocalCoreAt a s u v N d0 d1 x y := by
  unfold originalFirstDerivativeWickBilocalCoreAt originalDerivativeWickBilocalCoreAt
  rw [wick_scaled_finite_weighted_directional_derivative]
  · simp_rw [wickCoreChannelFirstMatrix_fderiv_right]
  · intro j hj
    exact (wickCoreChannelFirstMatrix_right_smooth a j.1 u v j.2 d0 x).differentiable (by simp) y

theorem originalWickBilocalCoreAt_mixed_fderiv (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ) (x y d0 d1 : Spacetime) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => originalWickBilocalCoreAt a s u v N w z) x d0) y d1 =
      originalDerivativeWickBilocalCoreAt a s u v N d0 d1 x y := by
  simp_rw [originalWickBilocalCoreAt_fderiv_left]
  exact originalFirstDerivativeWickBilocalCoreAt_fderiv_right a s u v N x y d0 d1

/-- Equality of original weak functions for every spacetime point propagates
through their actual derivatives. No moving-cutoff differentiation is used. -/
theorem originalDerivativeWickBilocalCore_eq_any_cutoff (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ)
    (hu : WickCoreTailBound u N) (hv : WickCoreTailBound v N)
    (d0 d1 x y : Spacetime) :
    originalDerivativeWickBilocalCore a s u v d0 d1 x y =
      originalDerivativeWickBilocalCoreAt a s u v N d0 d1 x y := by
  rw [← originalWickBilocalCore_mixed_fderiv]
  simp_rw [originalWickBilocalCore_eq_any_cutoff a s u v N hu hv]
  exact originalWickBilocalCoreAt_mixed_fderiv a s u v N x y d0 d1

theorem originalDerivativeWickMatrix_eq_any_cutoff (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (N : ℕ)
    (hu : WickCoreTailBound u N) (hv : WickCoreTailBound v N)
    (d0 d1 x : Spacetime) :
    originalDerivativeWickMatrix a s u v d0 d1 x =
      originalDerivativeWickBilocalCoreAt a s u v N d0 d1 x x :=
  originalDerivativeWickBilocalCore_eq_any_cutoff a s u v N hu hv d0 d1 x x

end AASCKleinGordon
