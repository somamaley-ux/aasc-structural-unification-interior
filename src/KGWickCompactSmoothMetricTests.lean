import KGOriginalWickActionResponse

/-! Every compact smooth real metric variation has its actual Schwartz
component family. No test-representation premise is required in this result. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_metric_component_hasCompactSupport (H : Spacetime → NativeRealMatrix)
    (hcomp : HasCompactSupport H) (i j : Fin 4) :
    HasCompactSupport (fun x => (H x i j : ℂ)) := by
  apply hcomp.mono
  intro x hx
  by_contra hz
  have hzero : H x=0 := by simpa only [Function.mem_support,not_not] using hz
  simpa [Function.mem_support,hzero] using hx

theorem wick_metric_component_smooth (H : Spacetime → NativeRealMatrix)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (i j : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (H x i j : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp ((nativeRealMatrixEntry i j).contDiff.comp hH)

def wickCompactSmoothMetricTestFamily (H : Spacetime → NativeRealMatrix)
    (hcomp : HasCompactSupport H) (hH : ContDiff ℝ (⊤ : ℕ∞) H) : WickSchwartzMetricTest :=
  fun i j => (wick_metric_component_hasCompactSupport H hcomp i j).toSchwartzMap
    (wick_metric_component_smooth H hH i j)

theorem wick_compact_smooth_metric_test_family_apply (H : Spacetime → NativeRealMatrix)
    (hcomp : HasCompactSupport H) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (x : Spacetime) (i j : Fin 4) :
    wickCompactSmoothMetricTestFamily H hcomp hH i j x=(H x i j : ℂ) := rfl

theorem original_wick_action_all_compact_smooth_metric_tests (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (H : Spacetime → NativeRealMatrix)
    (hcomp : HasCompactSupport H) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    (hsym : ∀ x i j,H x i j=H x j i) :
    HasDerivAt (originalWickScalarRelativeAction a s u v H)
      ((1/2 : ℂ)*originalWickStressMetricDistribution a s u v
        (wickCompactSmoothMetricTestFamily H hcomp hH)) 0 := by
  exact original_wick_action_derivative_eq_test_distribution a s u v H hH.continuous hcomp hsym
    (wickCompactSmoothMetricTestFamily H hcomp hH) (fun _ _ _ => rfl)

end AASCKleinGordon
