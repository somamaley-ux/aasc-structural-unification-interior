import WickNativeJointCoreContinuity
import WickStrongCoreControl

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

abbrev WickCoreStrongAntidual := FiniteParticleCore →L⋆[ℂ] ℂ
abbrev WickCoreStrongSourceOperators := FiniteParticleCore →L[ℂ] WickCoreStrongAntidual

def wickNativeTestEvaluationLM (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    (MetricSourceProbe Ω →L[ℝ] ℂ) →ₗ[ℂ] ℂ where
  toFun := fun F => F H
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def originalWickNativeAntidual (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (v : FiniteParticleCore) (H : MetricSourceProbe Ω) : WickCoreStrongAntidual where
  toLinearMap := (wickNativeTestEvaluationLM Ω H).comp
    ((originalWickNativeMetricSesq a s Ω).flip v)
  cont := by
    change Continuous (fun u : FiniteParticleCore => originalWickNativeMetricResponse a s u v Ω H)
    have hm : Continuous (fun u : FiniteParticleCore => ((u,v),H)) :=
      (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hc := (original_wick_native_response_joint_core_continuous a s Ω).comp hm
    simpa only [Function.comp_def] using hc

lemma original_wick_native_antidual_apply (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (v : FiniteParticleCore) (H : MetricSourceProbe Ω)
    (u : FiniteParticleCore) :
    originalWickNativeAntidual a s Ω v H u=originalWickNativeMetricResponse a s u v Ω H := rfl

/-- Abstract algebraic lift: continuity changes the packaging, not scalar laws. -/
def wickContinuousAntidualLinearLift {U V : Type*}
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] (U →ₗ⋆[ℂ] ℂ)) (hB : ∀ v,Continuous (B v)) :
    V →ₗ[ℂ] (U →L⋆[ℂ] ℂ) where
  toFun v := ⟨B v,hB v⟩
  map_add' v w := by
    apply ContinuousLinearMap.coe_injective
    exact B.map_add v w
  map_smul' c v := by
    apply ContinuousLinearMap.coe_injective
    exact B.map_smul c v

def originalWickNativeAlgebraicCoreOperator (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    FiniteParticleCore →ₗ[ℂ] (FiniteParticleCore →ₗ⋆[ℂ] ℂ) :=
  (originalWickNativeMetricSesq a s Ω).flip.compr₂ₛₗ (wickNativeTestEvaluationLM Ω H)

def originalWickNativeCoreOperatorLM (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (H : MetricSourceProbe Ω) : FiniteParticleCore →ₗ[ℂ] WickCoreStrongAntidual :=
  wickContinuousAntidualLinearLift (originalWickNativeAlgebraicCoreOperator a s Ω H) (fun v => by
    change Continuous (fun u : FiniteParticleCore => originalWickNativeMetricResponse a s u v Ω H)
    have hm : Continuous (fun u : FiniteParticleCore => ((u,v),H)) :=
      (continuous_id.prodMk continuous_const).prodMk continuous_const
    have hc := (original_wick_native_response_joint_core_continuous a s Ω).comp hm
    simpa only [Function.comp_def] using hc)

lemma original_wick_native_core_operator_strong_continuous (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) :
    Continuous (originalWickNativeCoreOperatorLM a s Ω H) := by
  apply wick_core_strong_continuous_of_bound
    (originalWickNativeCoreOperatorLM a s Ω H).toAddMonoidHom
    (fun v => wickOriginalRightCoreSeminorm a v*wickMetricTestL1 (nativeToWickMetricTest Ω H))
    ((wick_original_right_core_seminorm_continuous a).mul continuous_const)
    (by simp)
    (fun v => mul_nonneg (apply_nonneg _ _) (wick_metric_test_L1_nonnegative _))
    (wickNativeResponseLeftSeminorm a s) (wick_native_response_left_seminorm_continuous a s)
  intro v u
  change ‖originalWickNativeMetricResponse a s u v Ω H‖≤_
  exact (original_wick_native_response_continuous_controls_bound a s u v Ω H).trans_eq (by ring)

def originalWickNativeCoreOperator (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ))
    (H : MetricSourceProbe Ω) : WickCoreStrongSourceOperators :=
  ⟨originalWickNativeCoreOperatorLM a s Ω H,
    original_wick_native_core_operator_strong_continuous a s Ω H⟩

def originalWickNativeSourceOperatorLM (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    MetricSourceProbe Ω →ₗ[ℝ] WickCoreStrongSourceOperators where
  toFun := originalWickNativeCoreOperator a s Ω
  map_add' H K := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro u
    exact (originalWickNativeMetricResponse a s u v Ω).map_add H K
  map_smul' c H := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro u
    exact (originalWickNativeMetricResponse a s u v Ω).map_smul c H

lemma original_wick_native_source_operator_double_strong_continuous
    (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    Continuous (originalWickNativeSourceOperatorLM a s Ω) := by
  apply wick_core_double_strong_continuous_of_bound
    (originalWickNativeSourceOperatorLM a s Ω).toAddMonoidHom
    (fun H => wickMetricTestL1 (nativeToWickMetricTest Ω H))
    (native_wick_metric_test_L1_LF_continuous Ω) (by simp [wickMetricTestL1])
    (fun H => wick_metric_test_L1_nonnegative _)
    (wickNativeResponseLeftSeminorm a s) (wickOriginalRightCoreSeminorm a)
    (wick_native_response_left_seminorm_continuous a s)
    (wick_original_right_core_seminorm_continuous a)
  intro H v u
  change ‖originalWickNativeMetricResponse a s u v Ω H‖≤_
  exact (original_wick_native_response_continuous_controls_bound a s u v Ω H).trans_eq (by ring)

/-- The ORIGINAL half action response as an actual LF-test to strong-antidual
operator map, with bounded convergence at both operator levels. -/
def originalWickNativeStrongResponse (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    MetricSourceProbe Ω →L[ℝ] WickCoreStrongSourceOperators :=
  ⟨originalWickNativeSourceOperatorLM a s Ω,
    original_wick_native_source_operator_double_strong_continuous a s Ω⟩

/-- Full stress operator: the factor two restores the source tensor rather
than silently identifying it with the half action derivative. -/
def originalWickNativeFullStressOperator (a : Parameters) (s : ℝ) (Ω : Opens (Fin 4 → ℝ)) :
    MetricSourceProbe Ω →L[ℝ] WickCoreStrongSourceOperators :=
  originalWickNativeStrongResponse a s Ω+originalWickNativeStrongResponse a s Ω

lemma original_wick_native_strong_response_apply (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) (v u : FiniteParticleCore) :
    originalWickNativeStrongResponse a s Ω H v u=originalWickNativeMetricResponse a s u v Ω H := rfl

theorem original_wick_native_full_stress_operator_same_tensor (a : Parameters) (s : ℝ)
    (Ω : Opens (Fin 4 → ℝ)) (H : MetricSourceProbe Ω) (v u : FiniteParticleCore) :
    originalWickNativeFullStressOperator a s Ω H v u=
      originalWickStressMetricDistribution a s u v (nativeToWickMetricTest Ω H) := by
  change originalWickNativeMetricResponse a s u v Ω H+originalWickNativeMetricResponse a s u v Ω H=_
  rw [original_wick_native_metric_response_half_pairing]
  ring

end AASCKleinGordon
