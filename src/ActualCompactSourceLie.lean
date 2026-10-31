import ActualCompactCovariantGradient
import CompactSourceWardConstruction

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace
open scoped BigOperators

theorem coordinate_metric_lie_symmetric (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (X : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint) (a b : Fin 4) :
    coordinateMetricLieDerivative g X p a b = coordinateMetricLieDerivative g X p b a := by
  unfold coordinateMetricLieDerivative
  apply Finset.sum_congr rfl
  intro e _
  rw [metricPartial_symmetric g symmetric p a b e,
    symmetric p e a, symmetric p e b]
  ring

theorem compact_source_lie_tensor_is_actual (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (X : CoordinateVectorProbe Ω) (p : CoordinatePoint) (a b : Fin 4) :
    tensorEncode (compactMetricLieCLM Ω g hg X p) a b = coordinateMetricLieDerivative g X p a b := by
  have h (i : Fin 10) : compactMetricLieCLM Ω g hg X p i =
      coordinateMetricLieDerivative g X p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 := by
    have hp := congrArg (fun φ : ScalarSourceProbe Ω => φ p)
      (compact_metric_lie_projection Ω g hg i X)
    change compactMetricLieCLM Ω g hg X p i =
      compactMetricLieComponentCLM Ω g hg (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 X p at hp
    exact hp.trans (compact_metric_lie_component_apply Ω g hg _ _ X p)
  fin_cases a <;> fin_cases b <;>
    first
    | exact h _
    | exact (h _).trans (coordinate_metric_lie_symmetric g symmetric X p _ _)

#print axioms coordinate_metric_lie_symmetric
#print axioms compact_source_lie_tensor_is_actual
end
end AASCSemanticExhaustion
