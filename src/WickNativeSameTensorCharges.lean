import WickCalibratedChargeClosure
import WickNativeNormalizedSourceAssembly

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_native_tensor_same_raised_on_slice (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (j : Fin 4) (τ : ℝ) (x : WickSpaceSlice) :
    wickOriginalNativeRealTensor a s u
      (wickSpacetimeCoordinates (spacetimeSpatialJoin (τ,x))) 0 j=
        (originalWickScalarStressRaisedMatrix a s u u 0 j (spacetimeSpatialJoin (τ,x))).re := by
  unfold wickOriginalNativeRealTensor originalWickNativeStressDensity
  rw [ContinuousLinearEquiv.symm_apply_apply]

def wickNativeTensorHypersurfaceCharge (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (j : Fin 4) (τ : ℝ) : ℝ :=
  a.speed⁻¹*∫ x : WickSpaceSlice,wickOriginalNativeRealTensor a s u
    (wickSpacetimeCoordinates (spacetimeSpatialJoin (τ,x))) 0 j

theorem wick_native_tensor_hypersurface_same_charge (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (j : Fin 4) (τ : ℝ) :
    wickNativeTensorHypersurfaceCharge a s u j τ=(wickOriginalHypersurfaceCharge a s u u j τ).re := by
  unfold wickNativeTensorHypersurfaceCharge wickOriginalHypersurfaceCharge
  simp_rw [wick_native_tensor_same_raised_on_slice]
  have realIntegral := integral_re (wick_original_raised_stress_hypersurface_integrable a s u u j τ)
  change (∫ x : WickSpaceSlice,
    (originalWickScalarStressRaisedMatrix a s u u 0 j (spacetimeSpatialJoin (τ,x))).re)=
      (∫ x : WickSpaceSlice,
        originalWickScalarStressRaisedMatrix a s u u 0 j (spacetimeSpatialJoin (τ,x))).re at realIntegral
  rw [realIntegral,← Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- The tensor representing the SAME action-derived native source is the
one whose full four-channel hypersurface charge is the original Fock charge. -/
theorem wick_native_same_action_tensor_source_and_charge (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (j : Fin 4) (τ : ℝ) :
    (∀ H : MetricSourceProbe Ω,originalWickNativeRealMetricResponse a s u Ω H=
      (1/2 : ℝ)*∫ p,∑ i,∑ k,tensorEncode (H p) i k*wickOriginalNativeRealTensor a s u p i k) ∧
    wickNativeTensorHypersurfaceCharge a s u j τ=
      (wickSameTensorChargeCoefficient a s*
        inner ℂ (finiteParticleCoreToFock a u)
          (finiteParticleCoreToFock a (wickOriginalCoreFourMomentum a j u))).re := by
  refine ⟨wick_original_native_real_tensor_represents a s u Ω,?_⟩
  rw [wick_native_tensor_hypersurface_same_charge,wick_original_hypersurface_charge_fock_inner]

theorem wick_native_ray_presentation_source_and_charge (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (j : Fin 4) (τ : ℝ) :
    (∀ H : MetricSourceProbe Ω,(wickNativeRaySourcePresentation a s Ω ray).functional H=
      (1/2 : ℝ)*∫ p,∑ i,∑ k,tensorEncode (H p) i k*
        wickOriginalNativeRealTensor a s (wickRayPresentationState a ray) p i k) ∧
    wickNativeTensorHypersurfaceCharge a s (wickRayPresentationState a ray) j τ=
      (wickSameTensorChargeCoefficient a s*
        inner ℂ (finiteParticleCoreToFock a (wickRayPresentationState a ray))
          (finiteParticleCoreToFock a
            (wickOriginalCoreFourMomentum a j (wickRayPresentationState a ray)))).re := by
  have actual := wick_native_same_action_tensor_source_and_charge a s
    (wickRayPresentationState a ray) Ω j τ
  refine ⟨?_,actual.2⟩
  intro H
  rw [(wickNativeRaySourcePresentation a s Ω ray).same_original_source]
  exact actual.1 H

end AASCKleinGordon
