import WickOriginalLorentzMetricDomain

/-! The finite scalar metric-action readout itself, followed by its computed
Gâteaux differential. No derivative/source equality is an input field. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickOriginalFiniteAction (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) : ℂ :=
  ∫ x,wickQuantumActionDensity (wickOriginalFiniteMetric H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
    wickQuantumActionDensity wickFlatMetric
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)

theorem wick_native_metric_variation_smul {Ω : Opens CoordinatePoint}
    (r : ℝ) (H : MetricSourceProbe Ω) (x : Spacetime) :
    wickNativeMetricVariation (r • H) x=r • wickNativeMetricVariation H x :=
  tensorEncodeLinear.map_smul r (H (wickSpacetimeCoordinates x))

theorem wick_original_finite_action_on_direction (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (t : ℝ) :
    wickOriginalFiniteAction a s u v (t • H)=
      originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H) t := by
  unfold wickOriginalFiniteAction originalWickScalarRelativeAction
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simp only [wickOriginalFiniteMetric,wick_native_metric_variation_smul])

theorem wick_original_finite_action_gateaux_derivative (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => wickOriginalFiniteAction a s u v (t • H))
      (originalWickNativeStrongResponse a s Ω H v u) 0 := by
  have h := original_wick_native_strong_response_actual_action_derivative a s Ω H v u
  exact h.congr_of_eventuallyEq (Eventually.of_forall
    (wick_original_finite_action_on_direction a s u v H))

def wickOriginalRealFiniteAction (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) : ℝ :=
  (wickOriginalFiniteAction a s u u H).re

theorem wick_complex_derivative_real_part (f : ℝ → ℂ) (z : ℂ) (derivative : HasDerivAt f z 0) :
    HasDerivAt (fun t => (f t).re) z.re 0 :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 derivative

theorem wick_original_real_finite_action_gateaux_derivative (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => wickOriginalRealFiniteAction a s u (t • H))
      (originalWickNativeRealMetricResponse a s u Ω H) 0 := by
  have h : HasDerivAt (fun t : ℝ => wickOriginalFiniteAction a s u u (t • H))
      (originalWickNativeMetricResponse a s u u Ω H) 0 :=
    (original_wick_native_metric_response_actual_action_derivative a s u u Ω H).congr_of_eventuallyEq
      (Eventually.of_forall (wick_original_finite_action_on_direction a s u u H))
  change HasDerivAt (fun t : ℝ => (wickOriginalFiniteAction a s u u (t • H)).re)
    (originalWickNativeMetricResponse a s u u Ω H).re 0
  exact wick_complex_derivative_real_part _ _ h

def wickOriginalComputedGateaux (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) : ℝ :=
  deriv (fun t : ℝ => wickOriginalRealFiniteAction a s u (t • H)) 0

theorem wick_original_computed_gateaux_is_same_source (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickOriginalComputedGateaux a s u Ω H=originalWickNativeRealMetricResponse a s u Ω H :=
  (wick_original_real_finite_action_gateaux_derivative a s u Ω H).deriv

theorem wick_original_computed_gateaux_add (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H K : MetricSourceProbe Ω) :
    wickOriginalComputedGateaux a s u Ω (H+K)=
      wickOriginalComputedGateaux a s u Ω H+wickOriginalComputedGateaux a s u Ω K := by
  simp only [wick_original_computed_gateaux_is_same_source,map_add]

theorem wick_original_computed_gateaux_smul (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (r : ℝ) (H : MetricSourceProbe Ω) :
    wickOriginalComputedGateaux a s u Ω (r • H)=r*wickOriginalComputedGateaux a s u Ω H := by
  simp only [wick_original_computed_gateaux_is_same_source,map_smul,smul_eq_mul]

theorem wick_original_computed_gateaux_LF_continuous (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    Continuous (wickOriginalComputedGateaux a s u Ω) := by
  have same : wickOriginalComputedGateaux a s u Ω=originalWickNativeRealMetricResponse a s u Ω :=
    funext (wick_original_computed_gateaux_is_same_source a s u Ω)
  rw [same]
  exact (originalWickNativeRealMetricResponse a s u Ω).continuous

end AASCKleinGordon
