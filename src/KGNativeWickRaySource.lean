import KGNativeWickStateHomogeneity

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

abbrev WickNonzeroCore := {u : FiniteParticleCore // u≠0}

def wickCoreRaySetoid : Setoid WickNonzeroCore where
  r u v := ∃ z : ℂ,z≠0 ∧ v.val=z • u.val
  iseqv := by
    refine ⟨?_,?_,?_⟩
    · intro u
      exact ⟨1,one_ne_zero,by simp⟩
    · rintro u v ⟨z,hz,hv⟩
      refine ⟨z⁻¹,inv_ne_zero hz,?_⟩
      rw [hv,smul_smul,inv_mul_cancel₀ hz,one_smul]
    · rintro u v w ⟨z,hz,hv⟩ ⟨r,hr,hw⟩
      exact ⟨r*z,mul_ne_zero hr hz,by rw [hw,hv,smul_smul]⟩

def originalWickRayMetricResponse (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    Quotient wickCoreRaySetoid → (MetricSourceProbe Ω →L[ℝ] ℝ) :=
  Quotient.lift (fun u => originalWickNormalizedRayResponse a s u.val Ω) (by
    rintro u v ⟨z,hz,hv⟩
    dsimp only
    rw [hv,original_wick_normalized_ray_response_scalar_invariant a s z hz])

theorem original_wick_ray_source_on_representative (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u : WickNonzeroCore) :
    originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid u)=
      originalWickNormalizedRayResponse a s u.val Ω := rfl

theorem original_wick_ray_source_on_unit_representative (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u : WickNonzeroCore) (unit : ‖finiteParticleCoreToFock a u.val‖=1) :
    originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid u)=
      originalWickNativeRealMetricResponse a s u.val Ω := by
  simp [original_wick_ray_source_on_representative,originalWickNormalizedRayResponse,
    originalWickCoreNormSq,unit]

theorem original_wick_ray_source_LF_continuous (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (ray : Quotient wickCoreRaySetoid) :
    Continuous (originalWickRayMetricResponse a s Ω ray) :=
  (originalWickRayMetricResponse a s Ω ray).continuous

def originalWickRayRepresentedSource (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (ray : Quotient wickCoreRaySetoid) : SymmetricSourceComponents Ω :=
  representedMetricSource (originalWickRayMetricResponse a s Ω ray)

theorem original_wick_ray_source_representation (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    (1/2 : ℝ)*metricSourcePairing (originalWickRayRepresentedSource a s Ω ray) H=
      originalWickRayMetricResponse a s Ω ray H :=
  constructed_metric_source_represents _ H

/-- The homogeneous extension uses vector weights, a different domain from
physical rays. Its equality to the original tensor is proved for every nonzero
vector, rather than appending an independent quadratic source family. -/
theorem original_wick_ray_norm_squared_extension (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u : WickNonzeroCore) (H : MetricSourceProbe Ω) :
    originalWickCoreNormSq a u.val * originalWickRayMetricResponse a s Ω
      (Quotient.mk wickCoreRaySetoid u) H=
      originalWickNativeRealMetricResponse a s u.val Ω H := by
  exact congrArg (fun W : MetricSourceProbe Ω →L[ℝ] ℝ => W H)
    (original_wick_norm_squared_vector_extension a s u.val u.property Ω)

end AASCKleinGordon
