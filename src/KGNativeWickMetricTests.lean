import KGCompactTestSchwartz
import CompactMetricSourceRepresentation

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open scoped SchwartzMap Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickSpacetimeCoordinates : Spacetime ≃L[ℝ] (Fin 4 → ℝ) := EuclideanSpace.equiv (Fin 4) ℝ

def wickNativeMetricEntryCLM (i j : Fin 4) : (Fin 10 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.proj i).comp tensorEncodeLinear.toContinuousLinearMap))

def nativeToWickMetricTest (Ω : Opens (Fin 4 → ℝ)) :
    MetricSourceProbe Ω →L[ℝ] WickSchwartzMetricTest :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ wickSpacetimeCoordinates).comp
      ((wickCompactTestToSchwartzCLM Ω).comp
        (TestFunction.postcompCLM (wickNativeMetricEntryCLM i j)))))

theorem native_to_wick_metric_test_apply (Ω : Opens (Fin 4 → ℝ))
    (H : MetricSourceProbe Ω) (i j : Fin 4) (x : Spacetime) :
    nativeToWickMetricTest Ω H i j x=(tensorEncode (H (wickSpacetimeCoordinates x)) i j : ℂ) := rfl

theorem native_to_wick_metric_test_real (Ω : Opens (Fin 4 → ℝ))
    (H : MetricSourceProbe Ω) (i j : Fin 4) (x : Spacetime) :
    star (nativeToWickMetricTest Ω H i j x)=nativeToWickMetricTest Ω H i j x := by
  rw [native_to_wick_metric_test_apply]
  simp

def wickNativeMetricVariation {Ω : Opens (Fin 4 → ℝ)} (H : MetricSourceProbe Ω) :
    Spacetime → AASCSemanticExhaustion.NativeRealMatrix :=
  fun x => tensorEncode (H (wickSpacetimeCoordinates x))

theorem wick_native_metric_variation_smooth {Ω : Opens (Fin 4 → ℝ)} (H : MetricSourceProbe Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (wickNativeMetricVariation H) :=
  tensorEncodeLinear.toContinuousLinearMap.contDiff.comp (H.contDiff.comp wickSpacetimeCoordinates.contDiff)

theorem wick_native_metric_variation_compact {Ω : Opens (Fin 4 → ℝ)} (H : MetricSourceProbe Ω) :
    HasCompactSupport (wickNativeMetricVariation H) :=
  (H.hasCompactSupport.comp_left (g:=tensorEncode) (by ext i j;fin_cases i <;> fin_cases j <;> rfl)).comp_homeomorph
    wickSpacetimeCoordinates.toHomeomorph

theorem wick_native_metric_variation_symmetric {Ω : Opens (Fin 4 → ℝ)}
    (H : MetricSourceProbe Ω) (x : Spacetime) (i j : Fin 4) :
    wickNativeMetricVariation H x i j=wickNativeMetricVariation H x j i :=
  tensorEncode_symmetric _ i j

theorem native_to_wick_metric_test_LF_continuous (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (nativeToWickMetricTest Ω) := (nativeToWickMetricTest Ω).continuous

end AASCKleinGordon
