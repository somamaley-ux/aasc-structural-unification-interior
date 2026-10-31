import WickOriginalFiniteActionGateaux

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology Matrix.Norms.Operator
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickOriginalRelativeDensity (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) (x : Spacetime) : ℂ :=
  wickQuantumActionDensity (wickOriginalFiniteMetric H x)
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)-
    wickQuantumActionDensity wickFlatMetric
      (originalWickDerivativeComponents a s u v x) (originalWickMassSquare a s u v x)

theorem wick_original_relative_density_compact (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) {Ω : Opens CoordinatePoint} (H : MetricSourceProbe Ω) :
    HasCompactSupport (wickOriginalRelativeDensity a s u v H) := by
  apply (wick_native_metric_variation_compact H).mono'
  intro x hx
  by_contra outside
  have zero : wickOriginalRelativeDensity a s u v H x=0 := by
    unfold wickOriginalRelativeDensity
    rw [wick_original_finite_metric_off_support H x outside,sub_self]
  exact hx zero

theorem wick_original_relative_density_continuous (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω)
    (inside : H∈wickOriginalMetricNeighborhood Ω) :
    Continuous (wickOriginalRelativeDensity a s u v H) := by
  have hD := original_wick_derivative_components_continuous a s u v
  have hM := original_wick_mass_square_continuous a s u v
  have flat : wickFlatMetric.det≠0 := by rw [wick_flat_metric_det]; norm_num
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (wick_quantum_density_continuousAt (wickOriginalFiniteMetric H)
    (originalWickDerivativeComponents a s u v) (originalWickMassSquare a s u v)
    (wick_original_finite_metric_smooth H).continuous.continuousAt hD.continuousAt hM.continuousAt
    (wick_original_metric_domain_nondegenerate Ω H inside x)).sub
      (wick_quantum_density_continuousAt (fun _ : Spacetime => wickFlatMetric)
        (originalWickDerivativeComponents a s u v) (originalWickMassSquare a s u v)
        continuous_const.continuousAt hD.continuousAt hM.continuousAt flat)

theorem wick_original_finite_action_integrable (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω)
    (inside : H∈wickOriginalMetricNeighborhood Ω) :
    Integrable (wickOriginalRelativeDensity a s u v H) :=
  (wick_original_relative_density_continuous a s u v Ω H inside).integrable_of_hasCompactSupport
    (wick_original_relative_density_compact a s u v H)

theorem wick_original_finite_action_reparameterized (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω)
    (α : ℝ → ℝ) (c : ℝ) (zero : α 0=0) (derivative : HasDerivAt α c 0) :
    HasDerivAt (fun t => wickOriginalRealFiniteAction a s u (α t • H))
      (originalWickNativeRealMetricResponse a s u Ω (c • H)) 0 := by
  have h := wick_original_real_finite_action_gateaux_derivative a s u Ω H
  have hz : HasDerivAt (fun t : ℝ => wickOriginalRealFiniteAction a s u (t • H))
      (originalWickNativeRealMetricResponse a s u Ω H) (α 0) := by rw [zero];exact h
  have composed := hz.comp 0 derivative
  simpa only [Function.comp_def,map_smul,smul_eq_mul,mul_comm] using composed

theorem wick_original_reparameterized_direction_admitted (Ω : Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (α : ℝ → ℝ) (zero : α 0=0) (cont : ContinuousAt α 0) :
    ∀ᶠ t in 𝓝 0,α t • H∈wickOriginalMetricNeighborhood Ω := by
  have h := wick_original_metric_neighborhood_all_directions Ω H
  have ha : Tendsto α (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [ContinuousAt,zero] using cont
  exact ha.eventually h

theorem wick_original_fixed_compact_domain_open (Ω : Opens CoordinatePoint)
    (K : Compacts CoordinatePoint) (inside : (K : Set CoordinatePoint)⊆Ω) :
    IsOpen ((TestFunction.ofSupportedIn inside) ⁻¹' wickOriginalMetricNeighborhood Ω) :=
  (wick_original_metric_neighborhood_open Ω).preimage (TestFunction.continuous_ofSupportedIn inside)

end AASCKleinGordon
