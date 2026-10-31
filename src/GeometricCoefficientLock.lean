import DifferentiableTensorDivergence
import EinsteinCoefficientStep

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

def coordinateScalarGradient (g : MetricField) : CoordinatePoint :=
  fun b => scalarPartial (coordinateScalarCurvature g) 0 b

theorem c3_normal_divergence_ricci_germ (g : MetricField) (germ : C3NormalizedMetricGerm g) :
    coordinateDivergenceLinear g (ricciTensorGerm g germ) = (1 / 2 : ℝ) • coordinateScalarGradient g := by
  funext b
  exact c3_normal_coordinate_contracted_bianchi g germ b

theorem c3_normal_divergence_scalar_metric_germ (g : MetricField) (germ : C3NormalizedMetricGerm g) :
    coordinateDivergenceLinear g (scalarMetricTensorGerm g germ) = coordinateScalarGradient g := by
  funext b
  exact c3_normal_scalar_metric_divergence g germ b

theorem c3_normal_divergence_metric_germ (g : MetricField) (germ : C3NormalizedMetricGerm g) :
    coordinateDivergenceLinear g (metricTensorGerm g germ) = 0 := by
  have nd : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  funext b
  exact coordinate_metric_divergence_zero g 0 germ.1 nd b

/-- Bianchi and product/compatibility inputs are now derived from actual C³
geometry. Nonzero scalar gradient and vanishing response divergence remain
explicit. In particular the source Ward obligation is not renamed closedness. -/
theorem c3_normal_geometric_coefficient_lock_iff (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (gradient_nonzero : coordinateScalarGradient g ≠ 0) (a b c : ℝ) :
    coordinateDivergence g (a • coordinateRicci g + b • coordinateScalarMetric g + c • g) 0 = 0 ↔
      b = -a / 2 := by
  have h := MetricProjectionAudit.coefficient_lock_iff (coordinateDivergenceLinear g)
    (ricciTensorGerm g germ) (scalarMetricTensorGerm g germ) (metricTensorGerm g germ)
    (coordinateScalarGradient g) (c3_normal_divergence_ricci_germ g germ)
    (c3_normal_divergence_scalar_metric_germ g germ) (c3_normal_divergence_metric_germ g germ)
    gradient_nonzero a b c
  exact h

theorem c3_normal_geometric_einstein_combination (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (gradient_nonzero : coordinateScalarGradient g ≠ 0) (a b c : ℝ)
    (conserved : coordinateDivergence g (a • coordinateRicci g + b • coordinateScalarMetric g + c • g) 0 = 0) :
    b = -a / 2 ∧ a • coordinateRicci g + b • coordinateScalarMetric g + c • g =
      a • (coordinateRicci g - (1 / 2 : ℝ) • coordinateScalarMetric g) + c • g := by
  have hb := (c3_normal_geometric_coefficient_lock_iff g germ gradient_nonzero a b c).mp conserved
  refine ⟨hb, ?_⟩
  exact MetricProjectionAudit.einstein_combination (coordinateRicci g) (coordinateScalarMetric g) g a b c hb

#print axioms c3_normal_divergence_ricci_germ
#print axioms c3_normal_divergence_scalar_metric_germ
#print axioms c3_normal_divergence_metric_germ
#print axioms c3_normal_geometric_coefficient_lock_iff
#print axioms c3_normal_geometric_einstein_combination
end
end AASCSemanticExhaustion
