import NormalMetricInverseDifferentiable
import CoordinateConnectionCurvature

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 4096

theorem canonical_metric_square : metric * metric = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [metric, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem canonical_metric_inverse : metric⁻¹ = metric :=
  Matrix.inv_eq_right_inv canonical_metric_square

def normalLowerChristoffelDerivative (R : curvatureSpace) (a b c : Fin 4) :
    CoordinatePoint →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (normalMetricSecondDerivative R a c (Pi.single b 1) +
    normalMetricSecondDerivative R a b (Pi.single c 1) -
      normalMetricSecondDerivative R b c (Pi.single a 1))

theorem normal_metric_partial_linear (R : curvatureSpace) (x : CoordinatePoint) (a b c : Fin 4) :
    metricPartial (normalMetricPolynomial R) x a b c =
      normalMetricSecondDerivative R a b (Pi.single c 1) x := by
  unfold metricPartial
  rw [normalMetricPolynomial_fderiv]
  exact congrFun (normalMetricDerivative_eval_is_linear R a b (Pi.single c 1)) x

theorem normal_lowerChristoffel_linear (R : curvatureSpace) (a b c : Fin 4) :
    (fun x => lowerChristoffel (normalMetricPolynomial R) x a b c) =
      normalLowerChristoffelDerivative R a b c := by
  funext x
  simp [lowerChristoffel, normalLowerChristoffelDerivative, normal_metric_partial_linear]

theorem normal_lowerChristoffel_zero (R : curvatureSpace) (a b c : Fin 4) :
    lowerChristoffel (normalMetricPolynomial R) 0 a b c = 0 := by
  have h := congrFun (normal_lowerChristoffel_linear R a b c) 0
  simpa using h

theorem normal_lowerChristoffel_hasFDerivAt (R : curvatureSpace)
    (x : CoordinatePoint) (a b c : Fin 4) :
    HasFDerivAt (fun y => lowerChristoffel (normalMetricPolynomial R) y a b c)
      (normalLowerChristoffelDerivative R a b c) x := by
  rw [normal_lowerChristoffel_linear]
  exact (normalLowerChristoffelDerivative R a b c).hasFDerivAt

theorem normal_lowerChristoffel_derivative_basis (R : curvatureSpace) (a b c d : Fin 4) :
    normalLowerChristoffelDerivative R a b c (Pi.single d 1) =
      (1 / 2 : ℝ) * (normalMetricHessian R a c b d + normalMetricHessian R a b c d -
        normalMetricHessian R b c a d) := by
  simp [normalLowerChristoffelDerivative, normalMetricSecondDerivative_basis]

def normalChristoffelDerivative (R : curvatureSpace) (a b c : Fin 4) : CoordinatePoint →L[ℝ] ℝ :=
  ∑ d : Fin 4, metric a d • normalLowerChristoffelDerivative R d b c

theorem normal_christoffel_zero (R : curvatureSpace) (a b c : Fin 4) :
    leviCivitaCoefficients (normalMetricPolynomial R) 0 a b c = 0 := by
  simp [leviCivitaCoefficients, normal_lowerChristoffel_zero]

theorem normal_christoffel_hasFDerivAt_zero (R : curvatureSpace) (a b c : Fin 4) :
    HasFDerivAt (fun x => leviCivitaCoefficients (normalMetricPolynomial R) x a b c)
      (normalChristoffelDerivative R a b c) 0 := by
  have hd (d : Fin 4) := (normalMetric_inverse_differentiableAt_zero R a d).hasFDerivAt.mul
    (normal_lowerChristoffel_hasFDerivAt R 0 d b c)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun d _ => hd d)
  simpa only [normalChristoffelDerivative, leviCivitaCoefficients, Pi.mul_apply,
    normal_lowerChristoffel_zero, zero_smul, add_zero,
    normalMetricPolynomial_at_zero, canonical_metric_inverse] using hs

theorem normal_christoffel_fderiv_zero (R : curvatureSpace) (a b c : Fin 4) :
    fderiv ℝ (fun x => leviCivitaCoefficients (normalMetricPolynomial R) x a b c) 0 =
      normalChristoffelDerivative R a b c :=
  (normal_christoffel_hasFDerivAt_zero R a b c).fderiv

#print axioms canonical_metric_square
#print axioms canonical_metric_inverse
#print axioms normal_metric_partial_linear
#print axioms normal_lowerChristoffel_linear
#print axioms normal_lowerChristoffel_zero
#print axioms normal_lowerChristoffel_hasFDerivAt
#print axioms normal_lowerChristoffel_derivative_basis
#print axioms normal_christoffel_zero
#print axioms normal_christoffel_hasFDerivAt_zero
#print axioms normal_christoffel_fderiv_zero
end
end AASCSemanticExhaustion
