import KGNativeWickMetricResponse
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory TopologicalSpace
open scoped SchwartzMap
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_spacetime_coordinates_volume_preserving : MeasurePreserving wickSpacetimeCoordinates :=
  PiLp.volume_preserving_ofLp (Fin 4)

theorem wick_native_integral_coordinate_transport (f : (Fin 4 → ℝ) → ℂ) :
    (∫ x:Spacetime,f (wickSpacetimeCoordinates x))=∫ p,f p :=
  wick_spacetime_coordinates_volume_preserving.integral_comp
    wickSpacetimeCoordinates.toHomeomorph.measurableEmbedding f

def originalWickNativeStressDensity (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (p : Fin 4 → ℝ) (i j : Fin 4) : ℂ :=
  originalWickScalarStressRaisedMatrix a s u v i j (wickSpacetimeCoordinates.symm p)

theorem original_wick_native_tensor_test_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) (i j : Fin 4) :
    Integrable (fun p => (tensorEncode (H p) i j : ℂ)*originalWickNativeStressDensity a s u v p i j) := by
  apply (wick_spacetime_coordinates_volume_preserving.integrable_comp_emb
    wickSpacetimeCoordinates.toHomeomorph.measurableEmbedding).mp
  simpa only [Function.comp_def,originalWickNativeStressDensity,ContinuousLinearEquiv.symm_apply_apply,
    ← native_to_wick_metric_test_apply] using
    original_wick_raised_stress_test_integrable a s u v i j (nativeToWickMetricTest Ω H i j)

theorem original_wick_native_metric_response_tensor_density (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNativeMetricResponse a s u v Ω H=
      (1/2 : ℂ)*∫ p,∑ i,∑ j,(tensorEncode (H p) i j : ℂ)*originalWickNativeStressDensity a s u v p i j := by
  rw [original_wick_native_metric_response_half_pairing,original_wick_stress_metric_distribution_pairing]
  apply congrArg ((1/2 : ℂ)* ·)
  have ht := wick_native_integral_coordinate_transport
    (fun p => ∑ i,∑ j,(tensorEncode (H p) i j : ℂ)*originalWickNativeStressDensity a s u v p i j)
  simpa only [originalWickNativeStressDensity,ContinuousLinearEquiv.symm_apply_apply,
    native_to_wick_metric_test_apply] using ht

theorem original_wick_native_real_response_tensor_density (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNativeRealMetricResponse a s u Ω H=
      (1/2 : ℝ)*∫ p,∑ i,∑ j,tensorEncode (H p) i j*(originalWickNativeStressDensity a s u u p i j).re := by
  have hi := integrable_finset_sum (Finset.univ : Finset (Fin 4)) (fun i _ =>
    integrable_finset_sum (Finset.univ : Finset (Fin 4)) (fun j _ =>
      original_wick_native_tensor_test_integrable a s u u Ω H i j))
  change (originalWickNativeMetricResponse a s u u Ω H).re=_
  rw [original_wick_native_metric_response_tensor_density]
  have half (z : ℂ) : ((1/2 : ℂ)*z).re=(1/2 : ℝ)*z.re := by simp [Complex.mul_re]
  rw [half]
  have hr := (Complex.reCLM.integral_comp_comm hi).symm
  change (∫ p,∑ i,∑ j,(tensorEncode (H p) i j : ℂ)*originalWickNativeStressDensity a s u u p i j).re=
    ∫ p,(∑ i,∑ j,(tensorEncode (H p) i j : ℂ)*originalWickNativeStressDensity a s u u p i j).re at hr
  rw [hr]
  simp [Complex.mul_re]

end AASCKleinGordon
