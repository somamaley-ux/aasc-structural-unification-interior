import WickLocalOriginalCurveVariation
import OperationalMetricSourceAttachment

/-! An explicit finite-action compact C1 protocol receiver, fixed without a
response equation in its data. This is NOT an assertion that the receiver
exhausts an independently declared upstream protocol ledger. -/
noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

structure WickCompactC1MetricCurve (Ω : Opens CoordinatePoint) where
  tangentTest : MetricSourceProbe Ω
  curve : ℝ → Spacetime → NativeRealMatrix
  velocity : ℝ → Spacetime → NativeRealMatrix
  compact : Compacts Spacetime
  parameter : Set ℝ
  parameterOpen : IsOpen parameter
  parameterZero : (0:ℝ)∈parameter
  continuousCurve : ContinuousOn (fun z : ℝ × compact => curve z.1 z.2) (parameter ×ˢ univ)
  continuousVelocity : ContinuousOn (fun z : ℝ × compact => velocity z.1 z.2) (parameter ×ˢ univ)
  derivative : ∀ t∈parameter,∀ x,HasDerivAt (fun r => curve r x) (velocity t x) t
  base : ∀ x,curve 0 x=wickFlatMetric
  tangent : ∀ x,velocity 0 x=wickNativeMetricVariation tangentTest x
  support : ∀ᶠ t in 𝓝 (0:ℝ),∀ x,x∉compact → curve t x=wickFlatMetric

def wickStraightCompactCurve (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    WickCompactC1MetricCurve Ω where
  tangentTest := H
  curve t x := wickFlatMetric+t • wickNativeMetricVariation H x
  velocity _ x := wickNativeMetricVariation H x
  compact := ⟨tsupport (wickNativeMetricVariation H),wick_native_metric_variation_compact H⟩
  parameter := univ
  parameterOpen := isOpen_univ
  parameterZero := mem_univ _
  continuousCurve := (continuous_const.add (continuous_fst.smul
    ((wick_native_metric_variation_smooth H).continuous.comp
      (continuous_subtype_val.comp continuous_snd)))).continuousOn
  continuousVelocity := ((wick_native_metric_variation_smooth H).continuous.comp
    (continuous_subtype_val.comp continuous_snd)).continuousOn
  derivative t _ x := by
    simpa using ((hasDerivAt_id t).smul_const (wickNativeMetricVariation H x)).const_add wickFlatMetric
  base _ := by simp
  tangent _ := rfl
  support := Eventually.of_forall (fun t x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp)

theorem wick_straight_compact_curve_tangent (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    (wickStraightCompactCurve Ω H).tangentTest=H := rfl

def wickCompactCurveOutput (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (π : WickCompactC1MetricCurve Ω) : ℂ :=
  deriv (originalWickCurveRelativeAction a s u v π.curve) 0

theorem wick_compact_curve_output_is_same_strong_source (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickCompactC1MetricCurve Ω) :
    wickCompactCurveOutput a s u v π=
      originalWickNativeStrongResponse a s Ω π.tangentTest v u :=
  (original_wick_native_response_along_local_compact_C1_metric_curve a s u v Ω π.tangentTest
    π.curve π.velocity π.compact π.compact.isCompact π.parameter π.parameterOpen π.parameterZero
    π.continuousCurve π.continuousVelocity
    π.derivative π.base π.tangent π.support).deriv

theorem wick_compact_curve_output_presentation_independent (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint}
    (π ρ : WickCompactC1MetricCurve Ω) (same : π.tangentTest=ρ.tangentTest) :
    wickCompactCurveOutput a s u v π=wickCompactCurveOutput a s u v ρ :=
  (wick_compact_curve_output_is_same_strong_source a s u v π).trans
    ((congrArg (fun H => originalWickNativeStrongResponse a s Ω H v u) same).trans
      (wick_compact_curve_output_is_same_strong_source a s u v ρ).symm)

theorem wick_compact_curve_output_graph (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) (z : ℂ) :
    originalWickNativeStrongResponse a s Ω H v u=z ↔
      ∃ π : WickCompactC1MetricCurve Ω,π.tangentTest=H ∧ wickCompactCurveOutput a s u v π=z := by
  constructor
  · intro hz
    refine ⟨wickStraightCompactCurve Ω H,wick_straight_compact_curve_tangent Ω H,?_⟩
    exact (wick_compact_curve_output_is_same_strong_source a s u v (wickStraightCompactCurve Ω H)).trans
      ((congrArg (fun K => originalWickNativeStrongResponse a s Ω K v u)
        (wick_straight_compact_curve_tangent Ω H)).trans hz)
  · rintro ⟨π,ht,hz⟩
    exact (congrArg (fun K => originalWickNativeStrongResponse a s Ω K v u) ht).symm.trans
      ((wick_compact_curve_output_is_same_strong_source a s u v π).symm.trans hz)

theorem wick_compact_curve_real_output_on_tangent (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) {Ω : Opens CoordinatePoint} (π : WickCompactC1MetricCurve Ω)
    (H : MetricSourceProbe Ω) (ht : π.tangentTest=H) :
    (wickCompactCurveOutput a s u u π).re=originalWickNativeRealMetricResponse a s u Ω H := by
  have h := (wick_compact_curve_output_is_same_strong_source a s u u π).trans
    ((original_wick_native_strong_response_apply a s Ω π.tangentTest u u).trans
      (congrArg (fun K => originalWickNativeMetricResponse a s u u Ω K) ht))
  exact congrArg Complex.re h

/-- General packaging of an ALREADY COMPUTED finite-action output. The concrete
application below supplies `computed` by the integral-derivative theorem. -/
def wickCurveIncidenceOfComputedResponse {Ω : Opens CoordinatePoint} {P : Type*}
    (tangent : P → MetricSourceProbe Ω) (output : P → ℝ)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ)
    (total : ∀ H,∃ π,tangent π=H) (computed : ∀ π,output π=W (tangent π)) :
    OperationalMetricIncidence Ω P where
  incident H π := tangent π=H
  output := output
  total := total
  coherent H π ρ hp hr := by rw [computed,computed,hp,hr]
  add_compatible H K π ρ hp hr := by
    obtain ⟨σ,hσ⟩ := total (H+K)
    refine ⟨σ,hσ,?_⟩
    rw [computed,computed,computed,hσ,hp,hr,map_add]
  smul_compatible r H π hp := by
    obtain ⟨σ,hσ⟩ := total (r • H)
    refine ⟨σ,hσ,?_⟩
    rw [computed,computed,hσ,hp,map_smul,smul_eq_mul]

theorem wick_curve_incidence_computed_response {Ω : Opens CoordinatePoint} {P : Type*}
    (tangent : P → MetricSourceProbe Ω) (output : P → ℝ)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ)
    (total : ∀ H,∃ π,tangent π=H) (computed : ∀ π,output π=W (tangent π))
    (H : MetricSourceProbe Ω) :
    operationalMetricResponse (wickCurveIncidenceOfComputedResponse tangent output W total computed) H=W H := by
  obtain ⟨π,hπ⟩ := total H
  exact (operational_response_of_incident _ H π hπ).trans
    ((computed π).trans (congrArg W hπ))

def wickCompactCurveMetricIncidence (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) : OperationalMetricIncidence Ω (WickCompactC1MetricCurve Ω) :=
  wickCurveIncidenceOfComputedResponse WickCompactC1MetricCurve.tangentTest
    (fun π => (wickCompactCurveOutput a s u u π).re) (originalWickNativeRealMetricResponse a s u Ω)
    (fun H => ⟨wickStraightCompactCurve Ω H,wick_straight_compact_curve_tangent Ω H⟩)
    (fun π => wick_compact_curve_real_output_on_tangent a s u π π.tangentTest rfl)

theorem wick_compact_curve_operational_response_is_original (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    operationalMetricResponse (wickCompactCurveMetricIncidence a s u Ω) H=
      originalWickNativeRealMetricResponse a s u Ω H :=
  wick_curve_incidence_computed_response WickCompactC1MetricCurve.tangentTest
    (fun π => (wickCompactCurveOutput a s u u π).re) (originalWickNativeRealMetricResponse a s u Ω)
    (fun K => ⟨wickStraightCompactCurve Ω K,wick_straight_compact_curve_tangent Ω K⟩)
    (fun π => wick_compact_curve_real_output_on_tangent a s u π π.tangentTest rfl) H

end AASCKleinGordon
