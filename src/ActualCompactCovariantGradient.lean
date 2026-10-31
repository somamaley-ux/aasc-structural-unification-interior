import CompactMetricTestOperators

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace
open scoped BigOperators

/-- Identify the constructed test operator with the actual Levi-Civita
covariant derivative of the metric-lowered vector, wherever the metric is
nondegenerate. No connection or pairing bridge is received. -/
theorem compact_covariant_gradient_is_actual (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (X : CoordinateVectorProbe Ω) (p : CoordinatePoint) (nondegenerate : (g p).det ≠ 0)
    (a b : Fin 4) :
    compactCovariantGradientComponentCLM Ω g hg a b X p =
      coordinateCovectorDerivative (leviCivitaCoefficients g) (loweredCoordinateVector g X) p a b := by
  rw [compact_covariant_gradient_component_apply]
  unfold coordinateCovectorDerivative
  rw [lowered_coordinate_vector_partial g X p
    (fun c d => (hg c d).differentiable (by simp) p)
    (fun e => (compactVectorComponentCLM Ω e X).contDiff.differentiable (by simp) p)]
  have expand : (∑ r : Fin 4, leviCivitaCoefficients g p r a b * loweredCoordinateVector g X p r) =
      ∑ e : Fin 4, lowerChristoffel g p e a b * X p e := by
    simp only [loweredCoordinateVector, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, ← leviCivita_lowering g p nondegenerate e a b]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [symmetric p r e]
    ring
  rw [expand, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [lowerChristoffel_metric_compatibility g symmetric p b e a]
  ring

#print axioms compact_covariant_gradient_is_actual
end
end AASCSemanticExhaustion
