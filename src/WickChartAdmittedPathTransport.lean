import WickMetricPathPushforwardGeometry
import WickPoincareIncidence

/-! Transport the original admission set with all path operands. General D is
a coordinate-domain parameter, not a claim that arbitrary D is physically
licensed. The intended instances are the original neighborhood and its image. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

structure WickChartAdmittedMetricPath (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) where
  analytic : WickCompactC1MetricCurve Ω
  lift : ℝ → MetricSourceProbe Ω
  local_admitted : ∀ᶠ t in 𝓝 (0:ℝ),lift t ∈ D
  local_projection : ∀ᶠ t in 𝓝 (0:ℝ),∀ x,
    analytic.curve t x = wickOriginalFiniteMetric (lift t) x

def wickOriginalChartPath {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    WickChartAdmittedMetricPath Ω (wickOriginalMetricNeighborhood Ω) :=
  ⟨π.analytic,π.lift,π.local_admitted,π.local_projection⟩

def wickChartPathPoincare (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)}
    (π : WickChartAdmittedMetricPath Ω D) :
    WickChartAdmittedMetricPath (wickAffineMetricRegion b L Ω)
      (wickNativeAffineMetricTest b L '' D) where
  analytic := wickCompactCurvePoincare b L π.analytic
  lift t := wickNativeAffineMetricTest b L (π.lift t)
  local_admitted := π.local_admitted.mono (fun t ht => ⟨π.lift t,ht,rfl⟩)
  local_projection := by
    filter_upwards [π.local_projection] with t ht
    intro y
    let x := (wickPathAffineHomeomorph b L).symm y
    have recover : b+spacetimeLorentzCLE L x = y :=
      (wickPathAffineHomeomorph b L).apply_symm_apply y
    rw [← recover,wick_compact_curve_poincare_value,ht x]
    exact (wick_native_affine_finite_metric b L (π.lift t) x).symm

theorem wick_chart_path_actual_tangent {Ω : Opens CoordinatePoint}
    {D : Set (MetricSourceProbe Ω)} (π : WickChartAdmittedMetricPath Ω D) (x : Spacetime) :
    HasDerivAt (fun t => wickOriginalFiniteMetric (π.lift t) x)
      (wickNativeMetricVariation π.analytic.tangentTest x) 0 := by
  have actual := π.analytic.derivative 0 π.analytic.parameterZero x
  rw [π.analytic.tangent] at actual
  exact actual.congr_of_eventuallyEq (π.local_projection.mono (fun t ht => (ht x).symm))

theorem wick_chart_path_poincare_admission (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    ∀ᶠ t in 𝓝 (0:ℝ),
      (wickChartPathPoincare b L (wickOriginalChartPath π)).lift t ∈
        wickTransportedMetricDomain b L Ω :=
  (wickChartPathPoincare b L (wickOriginalChartPath π)).local_admitted

/-- All target first acts remain locally admitted, not merely the ones named
as images of chosen source acts. The transported chart is open and contains 0. -/
theorem wick_transported_chart_every_first_act_admitted (b : Spacetime)
    (L : ProperLorentzTransform) (Ω : Opens CoordinatePoint)
    (δ : WickKGFirstMetricAct (wickAffineMetricRegion b L Ω)) :
    ∀ᶠ t in 𝓝 (0:ℝ),δ.parameter t • δ.test ∈ wickTransportedMetricDomain b L Ω := by
  have zeroMap : wickNativeAffineMetricTest b L (0 : MetricSourceProbe Ω) = 0 := by
    simpa only [zero_smul] using wick_native_affine_test_smul b L 0 (0 : MetricSourceProbe Ω)
  have zeroInside : (0 : MetricSourceProbe (wickAffineMetricRegion b L Ω)) ∈
      wickTransportedMetricDomain b L Ω :=
    ⟨0,wick_original_metric_neighborhood_zero Ω,zeroMap⟩
  have continuous : ContinuousAt (fun t => δ.parameter t • δ.test) 0 :=
    δ.derivative.continuousAt.smul continuousAt_const
  have base : δ.parameter 0 • δ.test ∈ wickTransportedMetricDomain b L Ω := by
    simpa only [δ.parameter_zero,zero_smul] using zeroInside
  exact continuous ((wick_transported_metric_domain_open b L Ω).mem_nhds base)

theorem wick_chart_path_poincare_intrinsic_signature (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    ∀ᶠ t in 𝓝 (0:ℝ),∀ y,
      WickIntrinsicLorentzSignature
        (wickOriginalFiniteMetric ((wickChartPathPoincare b L (wickOriginalChartPath π)).lift t) y) ∧
      (wickOriginalFiniteMetric ((wickChartPathPoincare b L (wickOriginalChartPath π)).lift t) y).det ≠ 0 := by
  filter_upwards [wick_chart_path_poincare_admission b L π] with t inside
  intro y
  exact wick_transported_metric_signature b L Ω _ inside y

def wickChartPathOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)}
    (π : WickChartAdmittedMetricPath Ω D) : ℝ :=
  deriv (fun t => wickOriginalRealFiniteAction a s u (π.lift t)) 0

theorem wick_chart_path_actual_action_derivative (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)}
    (π : WickChartAdmittedMetricPath Ω D) :
    HasDerivAt (fun t => wickOriginalRealFiniteAction a s u (π.lift t))
      (originalWickNativeRealMetricResponse a s u Ω π.analytic.tangentTest) 0 := by
  have derivative := original_wick_native_response_along_local_compact_C1_metric_curve
    a s u u Ω π.analytic.tangentTest π.analytic.curve π.analytic.velocity
    π.analytic.compact π.analytic.compact.isCompact π.analytic.parameter
    π.analytic.parameterOpen π.analytic.parameterZero π.analytic.continuousCurve
    π.analytic.continuousVelocity π.analytic.derivative π.analytic.base
    π.analytic.tangent π.analytic.support
  rw [original_wick_native_strong_response_apply] at derivative
  have realDerivative := wick_complex_derivative_real_part _ _ derivative
  apply realDerivative.congr_of_eventuallyEq
  filter_upwards [π.local_projection] with t ht
  have metric : wickOriginalFiniteMetric (π.lift t) = π.analytic.curve t :=
    funext (fun x => (ht x).symm)
  unfold wickOriginalRealFiniteAction wickOriginalFiniteAction originalWickCurveRelativeAction
  rw [metric]

theorem wick_chart_path_output_computed (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} {D : Set (MetricSourceProbe Ω)}
    (π : WickChartAdmittedMetricPath Ω D) :
    wickChartPathOutput a s u π = originalWickNativeRealMetricResponse a s u Ω π.analytic.tangentTest :=
  (wick_chart_path_actual_action_derivative a s u π).deriv

theorem wick_chart_path_original_output (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (π : WickAdmittedC1MetricPath Ω) :
    wickChartPathOutput a s u (wickOriginalChartPath π) = wickAdmittedPathOutput a s u π := rfl

/-- Equality of actual finite action functions is proved pointwise first.
Neither a derivative equality nor a source naturality law is an input. -/
theorem wick_chart_path_action_poincare (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (b : Spacetime) (L : ProperLorentzTransform) {Ω : Opens CoordinatePoint}
    {D : Set (MetricSourceProbe Ω)} (π : WickChartAdmittedMetricPath Ω D) :
    (fun t => wickOriginalRealFiniteAction a s (corePoincare a b L u)
      ((wickChartPathPoincare b L π).lift t)) =
      (fun t => wickOriginalRealFiniteAction a s u (π.lift t)) :=
  funext (fun t => wick_original_real_finite_action_poincare a b L s u (π.lift t))

theorem wick_chart_path_output_poincare (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (b : Spacetime) (L : ProperLorentzTransform) {Ω : Opens CoordinatePoint}
    {D : Set (MetricSourceProbe Ω)} (π : WickChartAdmittedMetricPath Ω D) :
    wickChartPathOutput a s (corePoincare a b L u) (wickChartPathPoincare b L π) =
      wickChartPathOutput a s u π :=
  congrArg (fun f : ℝ → ℝ => deriv f 0) (wick_chart_path_action_poincare a s u b L π)

end AASCKleinGordon
