import KGWickMetricAdmissibility
import KGWickStressMetricDistribution

/-! A weak quantum metric response is the actual derivative of the fixed
action difference. Its continuous test-distribution representation is proved.
This does not assert the later real LF normalized-ray source/Ward package. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
open AASCSemanticExhaustion
namespace AASCKleinGordon

def originalWickMetricActionResponse (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (H : Spacetime → NativeRealMatrix) : ℂ :=
  deriv (originalWickScalarRelativeAction a s u v H) 0

theorem original_wick_action_response_eq_metric_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) (hsym : ∀ x i j,H x i j=H x j i) :
    originalWickMetricActionResponse a s u v H = (1/2 : ℂ)*originalWickRaisedMetricPairing a s u v H :=
  (original_wick_scalar_action_metric_first_variation a s u v H hH hcomp hsym).deriv

theorem original_wick_action_derivative_eq_test_distribution (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hH : Continuous H) (hcomp : HasCompactSupport H) (hsym : ∀ x i j,H x i j=H x j i)
    (k : WickSchwartzMetricTest) (hk : ∀ x i j,(H x i j : ℂ)=k i j x) :
    HasDerivAt (originalWickScalarRelativeAction a s u v H)
      ((1/2 : ℂ)*originalWickStressMetricDistribution a s u v k) 0 := by
  have hp : originalWickRaisedMetricPairing a s u v H=originalWickStressMetricDistribution a s u v k := by
    rw [original_wick_stress_metric_distribution_pairing]
    unfold originalWickRaisedMetricPairing
    simp_rw [hk]
  rw [← hp]
  exact original_wick_scalar_action_metric_first_variation a s u v H hH hcomp hsym

theorem original_wick_relative_action_at_zero (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix) :
    originalWickScalarRelativeAction a s u v H 0=0 := by
  simp [originalWickScalarRelativeAction]

theorem original_wick_relative_action_vacuum (a : Parameters) (s : ℝ)
    (H : Spacetime → NativeRealMatrix) (t : ℝ) :
    originalWickScalarRelativeAction a s vacuumCore vacuumCore H t=0 := by
  simp [originalWickScalarRelativeAction,wickQuantumActionDensity,originalWickDerivativeComponents,
    originalWickMassSquare,originalDerivativeWickMatrix_vacuum,originalWickSquareMatrix_vacuum]

theorem original_wick_metric_action_response_vacuum (a : Parameters) (s : ℝ)
    (H : Spacetime → NativeRealMatrix) :
    originalWickMetricActionResponse a s vacuumCore vacuumCore H=0 := by
  unfold originalWickMetricActionResponse
  have heq : originalWickScalarRelativeAction a s vacuumCore vacuumCore H=(fun _ : ℝ => (0 : ℂ)) :=
    funext (fun t => original_wick_relative_action_vacuum a s H t)
  rw [heq]
  simp

end AASCKleinGordon
