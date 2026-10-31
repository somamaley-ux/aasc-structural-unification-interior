import KGOriginalWickBilocalIdentification
import KGOriginalWickVacuumBaseline
import KGWickSeparateDerivativeKernels

/-! The complete ORIGINAL normal-ordered pair has an explicitly constructed
bilocal weak matrix on every original finite-core state. Its smooth diagonal
defines the Schwartz-tempered, distribution-valued sesquilinear Wick square.
No generic distribution restriction, new field/core/amplitude, classical EMT,
or assumed source/charge representation is introduced. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wickCoreChannelMatrix_left_smooth (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (y : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => wickCoreChannelMatrix a n u v i x y) :=
  wickLocalMatrix_smooth a (n+2) _ (wickCoreChannelFrequency0_temperate a n i) _

theorem wickCoreChannelMatrix_right_smooth (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (i : Fin 4) (x : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => wickCoreChannelMatrix a n u v i x y) := by
  unfold wickCoreChannelMatrix
  simp_rw [wickBilocalMatrix_swap a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i)]
  exact wickLocalMatrix_smooth a (n+2) _ (wickCoreChannelFrequency1_temperate a n i) _

theorem originalWickBilocalCore_left_smooth (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (y : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => originalWickBilocalCore a s u v x y) := by
  unfold originalWickBilocalCore
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (wickCoreChannelMatrix_left_smooth a j.1 u v j.2 y)

theorem originalWickBilocalCore_right_smooth (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (x : Spacetime) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => originalWickBilocalCore a s u v x y) := by
  unfold originalWickBilocalCore
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro j hj
  exact contDiff_const.mul (wickCoreChannelMatrix_right_smooth a j.1 u v j.2 x)

/-- A construction receipt with no received bilocal/diagonal bridge: all
objects are the explicit functions and test CLMs defined on the original core. -/
theorem original_local_wick_square_from_original_pair (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) :
    (∀ h k : 𝓢(Spacetime,ℂ),
      (∫ x,h x * ∫ y,k y * originalWickBilocalCore a s u v x y) =
        originalPairForm a s h k u v) ∧
    (∀ x,originalWickSquareMatrix a s u v x = originalWickBilocalCore a s u v x x) ∧
    ContDiff ℝ (⊤ : ℕ∞) (originalWickSquareMatrix a s u v) ∧
    (∀ h : 𝓢(Spacetime,ℂ), originalWickSquareDistributionSesqForm a s u v h =
      ∫ x,h x * originalWickBilocalCore a s u v x x) := by
  exact ⟨originalWickBilocalCore_smearing_eq_originalPairForm a s u v,
    fun _ => rfl,originalWickSquareMatrix_smooth a s u v,
    originalWickSquareDistributionSesqForm_pairing a s u v⟩

end AASCKleinGordon
