import WickNativeLieAttachment

noncomputable section
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem original_wick_native_real_lie_ward (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω) :
    originalWickNativeRealMetricResponse a s u Ω
      (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)=0 := by
  change (originalWickNativeMetricResponse a s u u Ω _).re=0
  rw [original_wick_native_lie_half_response_ward]
  rfl

/-- Actual distributional conservation follows from the proved same-tensor
Ward theorem and the constructed negative-dual covariant derivative. -/
theorem original_wick_native_represented_source_divergence_zero
    (a : Parameters) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    constructedSourceDivergence Ω wickNativeFlatMetric wick_native_flat_smooth
      (originalWickNativeRepresentedSource a s u Ω)=0 := by
  apply (constructed_source_closed_ward_iff Ω wickNativeFlatMetric wick_native_flat_smooth
    wick_native_flat_symmetric (originalWickNativeRealMetricResponse a s u Ω)).mp
  exact original_wick_native_real_lie_ward a s u Ω

theorem original_wick_native_lie_actual_action_stationary (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω) :
    HasDerivAt (originalWickScalarRelativeAction a s u v
      (wickNativeMetricVariation (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)))
      0 0 := by
  have h := original_wick_native_metric_response_actual_action_derivative a s u v Ω
    (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)
  simpa only [original_wick_native_lie_half_response_ward] using h

end AASCKleinGordon
