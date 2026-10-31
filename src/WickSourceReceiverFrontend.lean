import WickCalibratedOneParticleCasimir

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open TopologicalSpace
open scoped SchwartzMap BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_role_Qg_is_same_native_density (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) :
    wickRoleQg a s Ω (wickRolePiA a s Ω (wickRoleSx a s Ω ray))=
      originalWickNativeRepresentedSource a s (wickRayPresentationState a ray) Ω := by
  change wickRoleTA (wickRoleSx a s Ω ray)=representedMetricSource
    (originalWickNativeRealMetricResponse a s (wickRayPresentationState a ray) Ω)
  rw [wick_role_concrete_density_is_original]
  have same := original_wick_ray_source_is_actual_unit_response a s Ω ray.out
  rw [Quotient.out_eq] at same
  exact congrArg representedMetricSource same

/-- The structured quotient's concrete source really has the closed Ward
identity. It is not a proposition named 'closed' supplied to a receiver. -/
theorem wick_role_Qg_closed_divergence (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) :
    constructedSourceDivergence Ω wickNativeFlatMetric wick_native_flat_smooth
      (wickRoleQg a s Ω (wickRolePiA a s Ω (wickRoleSx a s Ω ray)))=0 := by
  rw [wick_role_Qg_is_same_native_density]
  exact original_wick_native_represented_source_divergence_zero a s (wickRayPresentationState a ray) Ω

theorem wick_role_source_actual_lie_stationarity (a : Parameters)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (X : CoordinateVectorProbe Ω) :
    HasDerivAt (originalWickScalarRelativeAction a (wickPositiveCalibratedAmplitude a)
      (wickRayPresentationState a ray) (wickRayPresentationState a ray)
      (wickNativeMetricVariation (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)))
      0 0 :=
  original_wick_native_lie_actual_action_stationary a (wickPositiveCalibratedAmplitude a)
    (wickRayPresentationState a ray) (wickRayPresentationState a ray) Ω X

/-- The transition source is an actual continuous Schwartz distribution of
the same action-derived tensor. No Breit/Green operator is postulated. -/
def wickCalibratedTransitionSource (a : Parameters) (u v : FiniteParticleCore) (i j : Fin 4) :
    𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  originalWickRaisedStressDistribution a (wickPositiveCalibratedAmplitude a) u v i j

theorem wick_calibrated_transition_source_continuous (a : Parameters)
    (u v : FiniteParticleCore) (i j : Fin 4) : Continuous (wickCalibratedTransitionSource a u v i j) :=
  (wickCalibratedTransitionSource a u v i j).continuous

theorem wick_calibrated_transition_source_conserved (a : Parameters)
    (u v : FiniteParticleCore) (j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    (∑ i,wickCalibratedTransitionSource a u v i j
      (wickDirectionalTestCLM (spacetimeCoordinateVector i) h))=0 :=
  original_wick_stress_distribution_conserved a (wickPositiveCalibratedAmplitude a) u v j h

end AASCKleinGordon
