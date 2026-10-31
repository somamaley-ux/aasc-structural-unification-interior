import KGNativeWickMetricTests

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open scoped SchwartzMap Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def originalWickNativeMetricResponse (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (Ω : Opens (Fin 4 → ℝ)) : MetricSourceProbe Ω →L[ℝ] ℂ :=
  (1/2 : ℂ) • ((originalWickStressMetricDistribution a s u v).restrictScalars ℝ).comp
    (nativeToWickMetricTest Ω)

def originalWickNativeRealMetricResponse (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens (Fin 4 → ℝ)) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  Complex.reCLM.comp (originalWickNativeMetricResponse a s u u Ω)

theorem original_wick_native_metric_response_half_pairing (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNativeMetricResponse a s u v Ω H=
      (1/2 : ℂ)*originalWickStressMetricDistribution a s u v (nativeToWickMetricTest Ω H) := rfl

theorem original_wick_native_metric_test_response_continuous (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (originalWickNativeRealMetricResponse a s u Ω) ∧
    ∀ H : MetricSourceProbe Ω,originalWickNativeRealMetricResponse a s u Ω H=
      (1/2 : ℝ)*(originalWickStressMetricDistribution a s u u (nativeToWickMetricTest Ω H)).re := by
  refine ⟨(originalWickNativeRealMetricResponse a s u Ω).continuous,?_⟩
  intro H
  simp [originalWickNativeRealMetricResponse,original_wick_native_metric_response_half_pairing,
    Complex.mul_re]

theorem original_wick_native_metric_response_actual_action_derivative (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    HasDerivAt (originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H))
      (originalWickNativeMetricResponse a s u v Ω H) 0 := by
  exact original_wick_action_derivative_eq_test_distribution a s u v (wickNativeMetricVariation H)
    (wick_native_metric_variation_smooth H).continuous (wick_native_metric_variation_compact H)
    (wick_native_metric_variation_symmetric H) (nativeToWickMetricTest Ω H) (fun _ _ _ => rfl)

theorem original_wick_native_real_response_actual_action (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNativeRealMetricResponse a s u Ω H=
      (originalWickMetricActionResponse a s u u (wickNativeMetricVariation H)).re := by
  exact congrArg Complex.re
    (original_wick_native_metric_response_actual_action_derivative a s u u Ω H).deriv.symm

def originalWickNativeRepresentedSource (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens (Fin 4 → ℝ)) : SymmetricSourceComponents Ω :=
  representedMetricSource (originalWickNativeRealMetricResponse a s u Ω)

theorem original_wick_native_source_half_pairing (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    (1/2 : ℝ)*metricSourcePairing (originalWickNativeRepresentedSource a s u Ω) H=
      (originalWickMetricActionResponse a s u u (wickNativeMetricVariation H)).re := by
  rw [originalWickNativeRepresentedSource,constructed_metric_source_represents]
  exact original_wick_native_real_response_actual_action a s u Ω H

end AASCKleinGordon
