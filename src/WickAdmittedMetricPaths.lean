import WickCurveRaySourceAttachment
import WickCommonRoleEvaluation

/-! A local metric-path completion of the declared free KG action branch.
The lift consists of actual original compact smooth symmetric metric tests;
local admission and uniform equality to their metric projections are required.
No source equation, action-germ equality or LF differentiability of the lift
is a field. This does not identify an unrestricted corpus response ledger. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

structure WickAdmittedC1MetricPath (Ω : Opens CoordinatePoint) where
  analytic : WickCompactC1MetricCurve Ω
  lift : ℝ → MetricSourceProbe Ω
  local_admitted : ∀ᶠ t in 𝓝 (0:ℝ),lift t ∈ wickOriginalMetricNeighborhood Ω
  local_projection : ∀ᶠ t in 𝓝 (0:ℝ),∀ x,
    analytic.curve t x = wickOriginalFiniteMetric (lift t) x

def wickAdmittedStraightPath (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    WickAdmittedC1MetricPath Ω where
  analytic := wickStraightCompactCurve Ω H
  lift t := t • H
  local_admitted := wick_original_metric_neighborhood_all_directions Ω H
  local_projection := Eventually.of_forall (fun t x => by
    change wickFlatMetric+t • wickNativeMetricVariation H x =
      wickFlatMetric+wickNativeMetricVariation (t • H) x
    rw [wick_native_metric_variation_smul])

/-- This is computed from the original finite action, before source attachment. -/
def wickAdmittedPathOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) : ℝ :=
  deriv (fun t => wickOriginalRealFiniteAction a s u (π.lift t)) 0

theorem wick_admitted_path_action_is_curve_germ (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    (fun t => wickOriginalFiniteAction a s u v (π.lift t)) =ᶠ[𝓝 (0:ℝ)]
      originalWickCurveRelativeAction a s u v π.analytic.curve := by
  filter_upwards [π.local_projection] with t ht
  have metric : wickOriginalFiniteMetric (π.lift t) = π.analytic.curve t :=
    funext (fun x => (ht x).symm)
  unfold wickOriginalFiniteAction originalWickCurveRelativeAction
  rw [metric]

theorem wick_admitted_path_actual_derivative (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    HasDerivAt (fun t => wickOriginalRealFiniteAction a s u (π.lift t))
      (originalWickNativeRealMetricResponse a s u Ω π.analytic.tangentTest) 0 := by
  have derivative := original_wick_native_response_along_local_compact_C1_metric_curve
    a s u u Ω π.analytic.tangentTest π.analytic.curve π.analytic.velocity
    π.analytic.compact π.analytic.compact.isCompact π.analytic.parameter
    π.analytic.parameterOpen π.analytic.parameterZero π.analytic.continuousCurve
    π.analytic.continuousVelocity π.analytic.derivative π.analytic.base
    π.analytic.tangent π.analytic.support
  have native := original_wick_native_strong_response_apply a s Ω π.analytic.tangentTest u u
  rw [native] at derivative
  have realDerivative := wick_complex_derivative_real_part _ _ derivative
  apply realDerivative.congr_of_eventuallyEq
  exact (wick_admitted_path_action_is_curve_germ a s u u π).mono
    (fun t ht => congrArg Complex.re ht)

theorem wick_admitted_path_output_computed (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    wickAdmittedPathOutput a s u π =
      originalWickNativeRealMetricResponse a s u Ω π.analytic.tangentTest :=
  (wick_admitted_path_actual_derivative a s u π).deriv

/-- Every added question is answered by an existing original first-act query.
The equality is proved from the integral derivative, not required as path data. -/
theorem wick_admitted_path_output_is_original_first (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    wickAdmittedPathOutput a s u π =
      wickKGFirstOutput a s u (wickKGIdentityAct π.analytic.tangentTest) := by
  rw [wick_admitted_path_output_computed,wick_KG_original_first_output_computed,
    wick_KG_identity_tangent]

theorem wick_admitted_path_every_tangent (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    ∃ π : WickAdmittedC1MetricPath Ω,π.analytic.tangentTest = H :=
  ⟨wickAdmittedStraightPath Ω H,rfl⟩

end AASCKleinGordon
