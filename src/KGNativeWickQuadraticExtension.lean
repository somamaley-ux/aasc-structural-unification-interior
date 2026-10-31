import KGNativeWickRaySource

/-! The quadratic vector-weight family is reconstructed from the normalized
ray response and proved equal to the original tensor response, including zero.
No independent quadratic source is appended. Joint graph continuity remains
a separate analytic obligation. -/
noncomputable section
set_option maxHeartbeats 8000000
open TopologicalSpace
open scoped SchwartzMap
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_sesq_diagonal_parallelogram {F : Type*} [AddCommGroup F] [Module ℂ F]
    (B : FiniteParticleCore →ₗ⋆[ℂ] FiniteParticleCore →ₗ[ℂ] F) (u v : FiniteParticleCore) :
    B (u+v) (u+v)+B (u-v) (u-v)=(2:ℂ) • B u u+(2:ℂ) • B v v := by
  simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply,two_smul]
  abel

theorem original_wick_raised_distribution_parallelogram (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    originalWickRaisedStressDistribution a s (u+v) (u+v) i j h+
      originalWickRaisedStressDistribution a s (u-v) (u-v) i j h=
      2*originalWickRaisedStressDistribution a s u u i j h+
        2*originalWickRaisedStressDistribution a s v v i j h := by
  have hp := congrArg (fun f : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ => f h)
    (wick_sesq_diagonal_parallelogram (originalWickScalarStressCandidateSesqForm a s i j) u v)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at hp
  simp only [originalWickRaisedStressDistribution,ContinuousLinearMap.smul_apply,smul_eq_mul]
  linear_combination ((wickFlatSign i : ℂ)*(wickFlatSign j : ℂ))*hp

theorem original_wick_metric_distribution_parallelogram (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (k : WickSchwartzMetricTest) :
    originalWickStressMetricDistribution a s (u+v) (u+v) k+
      originalWickStressMetricDistribution a s (u-v) (u-v) k=
      2*originalWickStressMetricDistribution a s u u k+
        2*originalWickStressMetricDistribution a s v v k := by
  simp only [originalWickStressMetricDistribution,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact original_wick_raised_distribution_parallelogram a s u v i j (k i j)

theorem original_wick_native_real_response_parallelogram (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeRealMetricResponse a s (u+v) Ω+originalWickNativeRealMetricResponse a s (u-v) Ω=
      (2:ℝ) • originalWickNativeRealMetricResponse a s u Ω+
        (2:ℝ) • originalWickNativeRealMetricResponse a s v Ω := by
  ext H
  have hp := original_wick_metric_distribution_parallelogram a s u v (nativeToWickMetricTest Ω H)
  have hr := congrArg Complex.re hp
  simp only [map_add,Complex.mul_re] at hr
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    (original_wick_native_metric_test_response_continuous a s (u+v) Ω).2,
    (original_wick_native_metric_test_response_continuous a s (u-v) Ω).2,
    (original_wick_native_metric_test_response_continuous a s u Ω).2,
    (original_wick_native_metric_test_response_continuous a s v Ω).2]
  norm_num at hr
  linarith

theorem original_wick_native_real_response_zero (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    originalWickNativeRealMetricResponse a s 0 Ω=0 := by
  simpa using original_wick_native_real_response_smul a s 0 (0:FiniteParticleCore) Ω

def originalWickVectorWeightResponse (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (u : FiniteParticleCore) : MetricSourceProbe Ω →L[ℝ] ℝ := by
  classical
  exact if hu:u=0 then 0 else originalWickCoreNormSq a u • originalWickRayMetricResponse a s Ω
    (Quotient.mk wickCoreRaySetoid ⟨u,hu⟩)

theorem original_wick_vector_weight_is_original_response (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u : FiniteParticleCore) :
    originalWickVectorWeightResponse a s Ω u=originalWickNativeRealMetricResponse a s u Ω := by
  classical
  by_cases hu:u=0
  · subst u
    simp [originalWickVectorWeightResponse,original_wick_native_real_response_zero]
  · simp only [originalWickVectorWeightResponse,hu,dif_neg]
    exact original_wick_norm_squared_vector_extension a s u hu Ω

theorem original_wick_vector_weight_parallelogram (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (u v : FiniteParticleCore) :
    originalWickVectorWeightResponse a s Ω (u+v)+originalWickVectorWeightResponse a s Ω (u-v)=
      (2:ℝ) • originalWickVectorWeightResponse a s Ω u+(2:ℝ) • originalWickVectorWeightResponse a s Ω v := by
  simp only [original_wick_vector_weight_is_original_response]
  exact original_wick_native_real_response_parallelogram a s u v Ω

end AASCKleinGordon
