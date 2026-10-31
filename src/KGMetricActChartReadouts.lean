import KGMetricActCharts

/-! Link the admitted metric-field chart equivalences to the original analytic
finite action and every first-response path. These are fixed free-KG chart
redescriptions, not an interaction or a change of the physical anchor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open TopologicalSpace AASCSemanticExhaustion Filter
open scoped Topology

def kgMetricActChartFiniteReadout (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (u : FiniteParticleCore) (H : KGMetricActChart q Ω) : ℝ :=
  wickOriginalRealFiniteAction a s (corePoincare a q.left.toAdd q.right u) H.val

theorem kg_metric_act_chart_finite_readout (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (u : FiniteParticleCore) (H : WickKGAdmittedFiniteMetric Ω) :
    kgMetricActChartFiniteReadout a s q Ω u (kgMetricActChartEquiv q Ω H)=
      wickOriginalRealFiniteAction a s u H.val :=
  wick_original_real_finite_action_poincare a q.left.toAdd q.right s u H.val

theorem kg_metric_act_chart_finite_comparison (a : Parameters) (s : ℝ)
    (p q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (u : FiniteParticleCore) (H : KGMetricActChart p Ω) :
    kgMetricActChartFiniteReadout a s q Ω u (kgMetricActChartChange p q Ω H)=
      kgMetricActChartFiniteReadout a s p Ω u H := by
  let K := (kgMetricActChartEquiv p Ω).symm H
  have recover : kgMetricActChartEquiv p Ω K=H :=
    (kgMetricActChartEquiv p Ω).apply_symm_apply H
  rw [← recover,kg_metric_act_chart_change_original,
    kg_metric_act_chart_finite_readout,kg_metric_act_chart_finite_readout]

theorem kg_metric_act_chart_first_direction_admitted (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint)
    (δ : WickKGFirstMetricAct (wickAffineMetricRegion q.left.toAdd q.right Ω)) :
    ∀ᶠ t in 𝓝 (0:ℝ),δ.parameter t • δ.test ∈
      wickTransportedMetricDomain q.left.toAdd q.right Ω :=
  wick_transported_chart_every_first_act_admitted q.left.toAdd q.right Ω δ

theorem kg_metric_act_chart_first_field_tangent (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (δ : WickKGFirstMetricAct Ω) (x : Spacetime) :
    HasDerivAt (fun t => wickKGFirstMetricCurve
      (wickKGFirstActPoincare q.left.toAdd q.right δ) t x)
      (wickNativeMetricVariation
        (wickNativeAffineMetricTest q.left.toAdd q.right (wickKGFirstTangent δ)) x) 0 := by
  rw [← wick_KG_poincare_tangent]
  exact wick_KG_original_act_tangent _ x

theorem kg_metric_act_chart_every_path_direction (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint)
    (J : MetricSourceProbe (wickAffineMetricRegion q.left.toAdd q.right Ω)) :
    ∃ π : WickAdmittedC1MetricPath Ω,
      (wickChartPathPoincare q.left.toAdd q.right
        (wickOriginalChartPath π)).analytic.tangentTest=J := by
  obtain ⟨π,same⟩ := wick_admitted_path_every_tangent Ω
    (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω J)
  refine ⟨π,?_⟩
  change wickNativeAffineMetricTest q.left.toAdd q.right π.analytic.tangentTest=J
  rw [same,wick_native_affine_inverse_right]

theorem kg_metric_act_chart_path_field (q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (π : WickAdmittedC1MetricPath Ω) :
    ∀ᶠ t in 𝓝 (0:ℝ),∀ x,
      (wickChartPathPoincare q.left.toAdd q.right (wickOriginalChartPath π)).analytic.curve t x=
        wickOriginalFiniteMetric
          ((wickChartPathPoincare q.left.toAdd q.right (wickOriginalChartPath π)).lift t) x :=
  (wickChartPathPoincare q.left.toAdd q.right (wickOriginalChartPath π)).local_projection

theorem kg_metric_act_chart_path_derivative (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (u : FiniteParticleCore) (π : WickAdmittedC1MetricPath Ω) :
    HasDerivAt (fun t => wickOriginalRealFiniteAction a s
      (corePoincare a q.left.toAdd q.right u)
      ((wickChartPathPoincare q.left.toAdd q.right (wickOriginalChartPath π)).lift t))
      (originalWickNativeRealMetricResponse a s u Ω π.analytic.tangentTest) 0 := by
  have actual := wick_chart_path_actual_action_derivative a s u (wickOriginalChartPath π)
  change HasDerivAt (fun t => wickOriginalRealFiniteAction a s u (π.lift t)) _ 0 at actual
  have same := wick_chart_path_action_poincare a s u q.left.toAdd q.right
    (wickOriginalChartPath π)
  rw [same]
  exact actual

theorem kg_metric_act_chart_path_output (a : Parameters) (s : ℝ)
    (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint)
    (u : FiniteParticleCore) (π : WickAdmittedC1MetricPath Ω) :
    wickChartPathOutput a s (corePoincare a q.left.toAdd q.right u)
      (wickChartPathPoincare q.left.toAdd q.right (wickOriginalChartPath π))=
      originalWickNativeRealMetricResponse a s u Ω π.analytic.tangentTest :=
  (kg_metric_act_chart_path_derivative a s q Ω u π).deriv

end AASCKleinGordon
