import KGNativeWickMetricResponse

noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open scoped SchwartzMap
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem original_wick_raised_distribution_smul_both (a : Parameters) (s : ℝ) (z : ℂ)
    (u v : FiniteParticleCore) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    originalWickRaisedStressDistribution a s (z • u) (z • v) i j h=
      ((‖z‖^2 : ℝ) : ℂ)*originalWickRaisedStressDistribution a s u v i j h := by
  have hc : star z*z=((‖z‖^2 : ℝ) : ℂ) := by
    simpa only [mul_comm,← Complex.ofReal_pow] using Complex.mul_conj' z
  simp only [originalWickRaisedStressDistribution,map_smulₛₗ,map_smul,
    LinearMap.smul_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,starRingEnd_apply,RingHom.id_apply]
  rw [← hc]
  ring

theorem original_wick_metric_distribution_smul_both (a : Parameters) (s : ℝ) (z : ℂ)
    (u v : FiniteParticleCore) (k : WickSchwartzMetricTest) :
    originalWickStressMetricDistribution a s (z • u) (z • v) k=
      ((‖z‖^2 : ℝ) : ℂ)*originalWickStressMetricDistribution a s u v k := by
  simp only [originalWickStressMetricDistribution,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    original_wick_raised_distribution_smul_both]
  simp_rw [← Finset.mul_sum]

theorem original_wick_native_response_smul_both (a : Parameters) (s : ℝ) (z : ℂ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNativeMetricResponse a s (z • u) (z • v) Ω H=
      ((‖z‖^2 : ℝ) : ℂ)*originalWickNativeMetricResponse a s u v Ω H := by
  simp only [original_wick_native_metric_response_half_pairing,original_wick_metric_distribution_smul_both]
  ring

theorem original_wick_native_real_response_smul (a : Parameters) (s : ℝ) (z : ℂ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeRealMetricResponse a s (z • u) Ω=
      (‖z‖^2 : ℝ) • originalWickNativeRealMetricResponse a s u Ω := by
  ext H
  change (originalWickNativeMetricResponse a s (z • u) (z • u) Ω H).re=_
  rw [original_wick_native_response_smul_both]
  change ((((‖z‖^2:ℝ):ℂ)*originalWickNativeMetricResponse a s u u Ω H).re)=
    ‖z‖^2*(originalWickNativeMetricResponse a s u u Ω H).re
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

def originalWickCoreNormSq (a : Parameters) (u : FiniteParticleCore) : ℝ :=
  ‖finiteParticleCoreToFock a u‖^2

theorem original_wick_core_norm_sq_positive (a : Parameters) (u : FiniteParticleCore) (hu : u≠0) :
    0<originalWickCoreNormSq a u := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  exact hu ((finiteParticleCoreToFock_injective a) (by simpa using hz))

theorem original_wick_core_norm_sq_smul (a : Parameters) (z : ℂ) (u : FiniteParticleCore) :
    originalWickCoreNormSq a (z • u)=‖z‖^2*originalWickCoreNormSq a u := by
  simp only [originalWickCoreNormSq,map_smul,norm_smul,mul_pow]

def originalWickNormalizedRayResponse (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens (Fin 4 → ℝ)) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  (originalWickCoreNormSq a u)⁻¹ • originalWickNativeRealMetricResponse a s u Ω

theorem original_wick_normalized_ray_response_scalar_invariant (a : Parameters) (s : ℝ)
    (z : ℂ) (hz : z≠0) (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNormalizedRayResponse a s (z • u) Ω=originalWickNormalizedRayResponse a s u Ω := by
  have hn : ‖z‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [originalWickNormalizedRayResponse,original_wick_core_norm_sq_smul,
    original_wick_native_real_response_smul,smul_smul]
  simp only [originalWickNormalizedRayResponse,mul_inv_rev]
  congr 1
  field_simp

theorem original_wick_normalized_ray_half_pairing (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    originalWickNormalizedRayResponse a s u Ω H=
      (originalWickCoreNormSq a u)⁻¹*((1/2 : ℝ)*
        (originalWickStressMetricDistribution a s u u (nativeToWickMetricTest Ω H)).re) := by
  exact congrArg ((originalWickCoreNormSq a u)⁻¹ * ·)
    ((original_wick_native_metric_test_response_continuous a s u Ω).2 H)

theorem original_wick_norm_squared_vector_extension (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (hu : u≠0) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickCoreNormSq a u • originalWickNormalizedRayResponse a s u Ω=
      originalWickNativeRealMetricResponse a s u Ω := by
  rw [originalWickNormalizedRayResponse,smul_smul,mul_inv_cancel₀
    (ne_of_gt (original_wick_core_norm_sq_positive a u hu)),one_smul]

end AASCKleinGordon
