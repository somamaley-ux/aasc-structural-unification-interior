import KGOriginalWickMixedDerivative

noncomputable section
set_option maxHeartbeats 4000000
namespace AASCKleinGordon

theorem wickCoreChannelMixedMatrix_diagonal (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 x : Spacetime) :
    wickCoreChannelMixedMatrix a n u v i d0 d1 x x =
      wickLocalMatrix a (n+2)
        (fun z => wickCoreChannelFrequency0 a n i z + wickCoreChannelFrequency1 a n i z)
        (wickCoreChannelMixedKernel a n u v i d0 d1) x :=
  wickBilocalMatrix_diagonal a (n+2) _ _ (wickCoreChannelFrequency1_temperate a n i) _ x

theorem wickCoreChannelMixedMatrix_diagonal_smooth (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (d0 d1 : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => wickCoreChannelMixedMatrix a n u v i d0 d1 x x) := by
  simp_rw [wickCoreChannelMixedMatrix_diagonal]
  exact wickLocalMatrix_smooth a (n+2) _
    ((wickCoreChannelFrequency0_temperate a n i).add
      (wickCoreChannelFrequency1_temperate a n i)) _

def originalDerivativeWickMatrix (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (d0 d1 x : Spacetime) : ℂ :=
  originalDerivativeWickBilocalCore a s u v d0 d1 x x

theorem originalDerivativeWickMatrix_eq_actual_mixed_diagonal (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 x : Spacetime) :
    originalDerivativeWickMatrix a s u v d0 d1 x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => originalWickBilocalCore a s u v z y) x d0) x d1 :=
  (originalWickBilocalCore_mixed_fderiv a s u v x x d0 d1).symm

theorem originalDerivativeWickMatrix_smooth (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (originalDerivativeWickMatrix a s u v d0 d1) := by
  unfold originalDerivativeWickMatrix originalDerivativeWickBilocalCore
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (wickCoreChannelMixedMatrix_diagonal_smooth a j.1 u v j.2 d0 d1)

end AASCKleinGordon
