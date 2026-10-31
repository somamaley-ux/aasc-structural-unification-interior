import WickDeclaredGraphTopology
import WickNativeStrongSourceAttachment
import WickNativeJointRayContinuity

noncomputable section
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- The constructed strong response is the actual original action derivative
for every native compact straight metric variation. -/
theorem original_wick_native_strong_response_actual_action_derivative
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (H : MetricSourceProbe Ω) (v u : FiniteParticleCore) :
    HasDerivAt (originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H))
      (originalWickNativeStrongResponse a s Ω H v u) 0 := by
  rw [original_wick_native_strong_response_apply]
  exact original_wick_native_metric_response_actual_action_derivative a s u v Ω H

/-- Explicit final attachment: proved graph equality, actual double-strong
continuous test map, actual original action derivative and same full tensor.
The protocol scope remains native compact straight metric variations. -/
theorem original_wick_native_graph_strong_source_attachment
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    wickDeclaredGraphTopology a=(inferInstance : TopologicalSpace FiniteParticleCore) ∧
    Continuous (originalWickNativeStrongResponse a s Ω) ∧
    (∀ (H : MetricSourceProbe Ω) (v u : FiniteParticleCore),
      HasDerivAt (originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H))
        (originalWickNativeStrongResponse a s Ω H v u) 0) ∧
    (∀ (H : MetricSourceProbe Ω) (v u : FiniteParticleCore),
      originalWickNativeFullStressOperator a s Ω H v u=
        originalWickStressMetricDistribution a s u v (nativeToWickMetricTest Ω H)) :=
  ⟨wick_declared_graph_topology_eq_original a,
    (originalWickNativeStrongResponse a s Ω).continuous,
    original_wick_native_strong_response_actual_action_derivative a s Ω,
    original_wick_native_full_stress_operator_same_tensor a s Ω⟩

end AASCKleinGordon
