import WickNativeJointCoreContinuity
noncomputable section
set_option maxHeartbeats 500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem original_wick_native_real_diagonal_joint_core_continuous
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (fun z : FiniteParticleCore × MetricSourceProbe Ω =>
      originalWickNativeRealMetricResponse a s z.1 Ω z.2) := by
  change Continuous (fun z : FiniteParticleCore × MetricSourceProbe Ω =>
    (originalWickNativeMetricResponse a s z.1 z.1 Ω z.2).re)
  have hm : Continuous (fun z : FiniteParticleCore × MetricSourceProbe Ω =>
      ((z.1,z.1),z.2)) :=
    (continuous_fst.prodMk continuous_fst).prodMk continuous_snd
  have hc := Complex.continuous_re.comp
    ((original_wick_native_response_joint_core_continuous a s Ω).comp hm)
  simpa only [Function.comp_def] using hc

theorem original_wick_vector_weight_response_joint_core_continuous
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (fun z : FiniteParticleCore × MetricSourceProbe Ω =>
      originalWickVectorWeightResponse a s Ω z.1 z.2) := by
  simpa only [original_wick_vector_weight_is_original_response] using
    original_wick_native_real_diagonal_joint_core_continuous a s Ω

theorem original_wick_unit_ray_evaluation_joint_core_continuous
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (fun z : WickNonzeroCore × MetricSourceProbe Ω =>
      originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid z.1) z.2) := by
  have hc := (original_wick_native_real_diagonal_joint_core_continuous a s Ω).comp
    (((original_wick_unit_representative_core_continuous a).comp continuous_fst).prodMk continuous_snd)
  have he : (fun z : WickNonzeroCore × MetricSourceProbe Ω =>
      originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid z.1) z.2)=
      (fun z => originalWickNativeRealMetricResponse a s
        (originalWickUnitRepresentative a z.1.val) Ω z.2) := by
    funext z
    exact congrArg (fun W : MetricSourceProbe Ω →L[ℝ] ℝ => W z.2)
      (original_wick_ray_source_is_actual_unit_response a s Ω z.1)
  rw [he]
  simpa only [Function.comp_def] using hc

end AASCKleinGordon
