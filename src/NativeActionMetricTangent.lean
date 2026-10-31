import NativeActionCurveProtocol
import CompactSourceWardConstruction

/-! The metric tangent map is an actual derivative of the affine metric
projection from the LF deformation carrier. All compact symmetric probes
have original straight paths, admitted near zero in every declared open
metric/action domain. Dimension/signature and openness remain branch data. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction

variable {Ω : Opens CoordinatePoint}

def nativeMetricComponentEvaluation (p : CoordinatePoint) (a b : Fin 4) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj (sourceSymmetricIndex a b)) : (Fin 10 → ℝ) →L[ℝ] ℝ).comp
    (((BoundedContinuousFunction.evalCLM ℝ p) :
      (CoordinatePoint →ᵇ (Fin 10 → ℝ)) →L[ℝ] (Fin 10 → ℝ)).comp
      (TestFunction.toBoundedContinuousFunctionCLM ℝ))

theorem native_metric_component_evaluation (h : MetricSourceProbe Ω)
    (p : CoordinatePoint) (a b : Fin 4) :
    nativeMetricComponentEvaluation p a b h = tensorEncode (h p) a b := by
  fin_cases a <;> fin_cases b <;> rfl

def nativeActionMetricProjection (g : MetricField) (h : MetricSourceProbe Ω) : MetricField :=
  fun p a b => g p a b + tensorEncode (h p) a b

theorem native_action_metric_projection_symmetric (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (h : MetricSourceProbe Ω) :
    MetricFieldSymmetric (nativeActionMetricProjection g h) := by
  intro p a b
  simp only [nativeActionMetricProjection,symmetric p a b,tensorEncode_symmetric (h p) a b]

theorem native_action_curve_actual_metric_tangent (g : MetricField)
    (π : NativeActionCurve (MetricSourceProbe Ω)) (p : CoordinatePoint) (a b : Fin 4) :
    HasDerivAt (fun t => nativeActionMetricProjection g (π.curve t) p a b)
      (tensorEncode (π.tangent p) a b) 0 := by
  let ev : MetricSourceProbe Ω →L[ℝ] ℝ := nativeMetricComponentEvaluation p a b
  have ht := (ev.continuous.tendsto π.tangent).comp π.tangent_limit
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have heq : (fun t : ℝ => t⁻¹ •
      (nativeActionMetricProjection g (π.curve (0+t)) p a b -
        nativeActionMetricProjection g (π.curve 0) p a b)) =
      (fun t : ℝ => ev (t⁻¹ • π.curve t)) := by
    funext t
    rw [map_smul]
    simp only [nativeActionMetricProjection,zero_add,π.base,
      ← native_metric_component_evaluation, map_zero,add_zero,add_sub_cancel_left]
    rfl
  rw [heq]
  simpa only [ev,Function.comp_def,native_metric_component_evaluation] using ht

theorem native_action_all_metric_probes_have_actual_admitted_paths
    (g : MetricField) (U : Opens (MetricSourceProbe Ω)) (base : (0:MetricSourceProbe Ω)∈U)
    (h : MetricSourceProbe Ω) :
    ∃ π : NativeActionCurve (MetricSourceProbe Ω), π.tangent=h ∧
      (∀ᶠ t in 𝓝 0, π.curve t∈U) ∧
      ∀ p a b, HasDerivAt (fun t => nativeActionMetricProjection g (π.curve t) p a b)
        (tensorEncode (h p) a b) 0 := by
  exact ⟨nativeStraightActionCurve h,rfl,
    native_action_curve_locally_admitted U base _,native_action_curve_actual_metric_tangent g _⟩

#print axioms native_metric_component_evaluation
#print axioms native_action_metric_projection_symmetric
#print axioms native_action_curve_actual_metric_tangent
#print axioms native_action_all_metric_probes_have_actual_admitted_paths
end
end AASCSemanticExhaustion
