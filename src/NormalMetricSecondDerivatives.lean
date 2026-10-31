import NormalMetricDerivatives

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 4096

def normalMetricSecondDerivative (R : curvatureSpace) (a b : Fin 4)
    (v : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ c : Fin 4, ∑ d : Fin 4,
    normalMetricHessian R a b c d •
      (v d • coordinateProjection c + v c • coordinateProjection d)

theorem normalMetricDerivative_eval_is_linear (R : curvatureSpace) (a b : Fin 4)
    (v : Fin 4 → ℝ) :
    (fun x => normalMetricDerivative R x a b v) = normalMetricSecondDerivative R a b v := by
  funext x
  simp [normalMetricDerivative, normalMetricSecondDerivative, coordinateProjection, mul_comm]

theorem normalMetricDerivative_eval_hasFDerivAt (R : curvatureSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) (v : Fin 4 → ℝ) :
    HasFDerivAt (fun y => normalMetricDerivative R y a b v)
      (normalMetricSecondDerivative R a b v) x := by
  rw [normalMetricDerivative_eval_is_linear]
  exact (normalMetricSecondDerivative R a b v).hasFDerivAt

theorem normalMetricSecondDerivative_basis (R : curvatureSpace) (a b c d : Fin 4) :
    normalMetricSecondDerivative R a b (Pi.single c 1) (Pi.single d 1) =
      normalMetricHessian R a b c d := by
  simp [normalMetricSecondDerivative, coordinateProjection, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, ite_mul, mul_ite]
  rw [normalMetricHessian_derivative_symmetry R a b d c]
  ring

/-- Actual component second Frechet derivative, not a formal Hessian label. -/
theorem normalMetricPolynomial_second_derivative (R : curvatureSpace)
    (a b c d : Fin 4) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => normalMetricPolynomial R y a b) x
      (Pi.single c 1)) 0 (Pi.single d 1) = normalMetricHessian R a b c d := by
  simp_rw [normalMetricPolynomial_fderiv]
  rw [(normalMetricDerivative_eval_hasFDerivAt R 0 a b (Pi.single c 1)).fderiv]
  exact normalMetricSecondDerivative_basis R a b c d

#print axioms normalMetricDerivative_eval_is_linear
#print axioms normalMetricDerivative_eval_hasFDerivAt
#print axioms normalMetricSecondDerivative_basis
#print axioms normalMetricPolynomial_second_derivative
end
end AASCSemanticExhaustion
