import KGOriginalDerivativeWickSmearing
import KGDerivativeWickVacuumBaseline

/-! Derivative-Wick products are constructed from the SAME original bilocal
pair on arbitrary original core states. Actual differentiation, smearing,
coincidence, regularity, state laws and covering-cutoff identity are proved.
No quantum stress/action/source/charge matching is assumed. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem original_derivative_wick_from_original_pair (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (d0 d1 : Spacetime) :
    (∀ h k : 𝓢(Spacetime,ℂ),
      (∫ x,h x * ∫ y,k y * originalDerivativeWickBilocalCore a s u v d0 d1 x y) =
        originalPairForm a s (wickDirectionalTestCLM d0 h) (wickDirectionalTestCLM d1 k) u v) ∧
    (∀ x,originalDerivativeWickMatrix a s u v d0 d1 x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => originalWickBilocalCore a s u v z y) x d0) x d1) ∧
    ContDiff ℝ (⊤ : ℕ∞) (originalDerivativeWickMatrix a s u v d0 d1) ∧
    (∀ h : 𝓢(Spacetime,ℂ),originalDerivativeWickDistributionSesqForm a s d0 d1 u v h =
      ∫ x,h x * originalDerivativeWickMatrix a s u v d0 d1 x) ∧
    (∀ (N : ℕ) (hu : WickCoreTailBound u N) (hv : WickCoreTailBound v N)
      (h : 𝓢(Spacetime,ℂ)),originalDerivativeWickDistribution a s u v d0 d1 h =
      ∫ x,h x * originalDerivativeWickBilocalCoreAt a s u v N d0 d1 x x) := by
  exact ⟨originalDerivativeWickBilocalCore_smearing_eq_originalPairForm a s u v d0 d1,
    originalDerivativeWickMatrix_eq_actual_mixed_diagonal a s u v d0 d1,
    originalDerivativeWickMatrix_smooth a s u v d0 d1,
    originalDerivativeWickDistributionSesqForm_pairing a s u v d0 d1,
    fun N hu hv => originalDerivativeWickDistribution_any_cutoff_pairing a s u v N hu hv d0 d1⟩

end AASCKleinGordon
