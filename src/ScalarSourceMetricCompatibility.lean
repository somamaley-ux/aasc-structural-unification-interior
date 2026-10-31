import ScalarFieldSourceBalance
import GeometricCoefficientLock

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Filter
open scoped Topology

theorem coordinate_divergence_germ_congruence (g T U : MetricField)
    (equal_near : T =ᶠ[nhds 0] U) : coordinateDivergence g T 0 = coordinateDivergence g U 0 := by
  have value : T 0 = U 0 := Filter.EventuallyEq.eq_of_nhds equal_near
  have derivative (a b : Fin 4) :
      fderiv ℝ (fun x => T x a b) 0 = fderiv ℝ (fun x => U x a b) 0 := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [equal_near] with x hx
    exact congrArg (fun A : Tensor2 => A a b) hx
  funext b
  simp only [coordinateDivergence, coordinateCovariantTensorDerivative, scalarPartial, derivative, value]

/-- A genuine field equation on a neighborhood, not equality only at one
point, transfers the derived scalar-source conservation to geometry. -/
theorem scalar_source_matching_implies_geometric_conservation
    (g E : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ κ : ℝ)
    (internal_equation : scalarFieldWaveOperator g φ 0 = μ * φ 0)
    (field_matching : E =ᶠ[nhds 0] κ • scalarFieldStress g φ μ) :
    coordinateDivergence g E 0 = 0 := by
  rw [coordinate_divergence_germ_congruence g E _ field_matching,
    coordinateDivergence_smul_at_zero g _ κ (c2_normal_scalar_stress_differentiable g germ φ hφ μ),
    c2_normal_scalar_internal_equation_implies_conservation g germ φ hφ μ internal_equation,
    smul_zero]

/-- Einstein 19.8 and 23.1 for the actual scalar source subclass. Conservation
is discharged from the internal field equation. Occupation of a general
nonzero-gradient metric/source family is still an independent native burden. -/
theorem scalar_source_matching_locks_geometric_coefficients
    (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (gradient_nonzero : coordinateScalarGradient g ≠ 0)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ κ a b c : ℝ)
    (internal_equation : scalarFieldWaveOperator g φ 0 = μ * φ 0)
    (field_matching : (a • coordinateRicci g + b • coordinateScalarMetric g + c • g)
      =ᶠ[nhds 0] κ • scalarFieldStress g φ μ) : b = -a / 2 := by
  apply (c3_normal_geometric_coefficient_lock_iff g germ gradient_nonzero a b c).mp
  exact scalar_source_matching_implies_geometric_conservation g _ (c3_normalized_metric_c2 g germ)
    φ hφ μ κ internal_equation field_matching

#print axioms coordinate_divergence_germ_congruence
#print axioms scalar_source_matching_implies_geometric_conservation
#print axioms scalar_source_matching_locks_geometric_coefficients
end
end AASCSemanticExhaustion
