import NormalLeviCivitaJet

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem canonical_metric_double_contraction (v : Fin 4 → ℝ) (a : Fin 4) :
    (∑ e : Fin 4, metric a e * (∑ f : Fin 4, metric e f * v f)) = v a := by
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ f : Fin 4, (metric * metric) a f * v f) = _
  rw [canonical_metric_square]
  simp [Matrix.one_apply, ite_mul]

theorem normal_christoffel_derivative_lowering (R : curvatureSpace)
    (a b c : Fin 4) (v : CoordinatePoint) :
    (∑ e : Fin 4, metric a e * normalChristoffelDerivative R e b c v) =
      normalLowerChristoffelDerivative R a b c v := by
  simpa [normalChristoffelDerivative] using
    canonical_metric_double_contraction (fun f => normalLowerChristoffelDerivative R f b c v) a

theorem normal_curvature_is_lowerChristoffel_derivative (R : curvatureSpace)
    (a b c d : Fin 4) :
    loweredConnectionCurvature (normalMetricPolynomial R)
      (leviCivitaCoefficients (normalMetricPolynomial R)) 0 a b c d =
      normalLowerChristoffelDerivative R a d b (Pi.single c 1) -
        normalLowerChristoffelDerivative R a c b (Pi.single d 1) := by
  simp only [loweredConnectionCurvature, connectionCurvature,
    normal_christoffel_zero, zero_mul, Finset.sum_const_zero, add_zero, sub_zero,
    normalMetricPolynomial_at_zero, normal_christoffel_fderiv_zero,
    mul_sub, Finset.sum_sub_distrib]
  rw [normal_christoffel_derivative_lowering, normal_christoffel_derivative_lowering]

theorem normal_leviCivita_curvature_formula (R : curvatureSpace) (a b c d : Fin 4) :
    loweredConnectionCurvature (normalMetricPolynomial R)
      (leviCivitaCoefficients (normalMetricPolynomial R)) 0 a b c d =
        curvatureOfNormalHessian (normalMetricHessian R) a b c d := by
  rw [normal_curvature_is_lowerChristoffel_derivative,
    normal_lowerChristoffel_derivative_basis, normal_lowerChristoffel_derivative_basis]
  unfold curvatureOfNormalHessian
  rw [normalMetricHessian_derivative_symmetry R a b d c,
    normalMetricHessian_metric_symmetry R d b a c,
    normalMetricHessian_metric_symmetry R c b a d]
  ring

theorem normal_leviCivita_curvature_realizes_original (R : curvatureSpace) :
    loweredConnectionCurvature (normalMetricPolynomial R)
      (leviCivitaCoefficients (normalMetricPolynomial R)) 0 = (R : Tensor4) := by
  funext a b c d
  rw [normal_leviCivita_curvature_formula]
  exact congrFun (congrFun (congrFun (congrFun
    (curvature_of_constructed_normal_hessian R) a) b) c) d

#print axioms canonical_metric_double_contraction
#print axioms normal_christoffel_derivative_lowering
#print axioms normal_curvature_is_lowerChristoffel_derivative
#print axioms normal_leviCivita_curvature_formula
#print axioms normal_leviCivita_curvature_realizes_original
end
end AASCSemanticExhaustion
