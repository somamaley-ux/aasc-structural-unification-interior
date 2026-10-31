import NormalMetricPolynomial
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators

def coordinateProjection (c : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj c

def normalMetricDerivative (R : curvatureSpace) (x : Fin 4 → ℝ) (a b : Fin 4) :
    (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ c : Fin 4, ∑ d : Fin 4,
    normalMetricHessian R a b c d •
      (x c • coordinateProjection d + x d • coordinateProjection c)

theorem normalMetricPolynomial_hasFDerivAt (R : curvatureSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) :
    HasFDerivAt (fun y => normalMetricPolynomial R y a b)
      (normalMetricDerivative R x a b) x := by
  have h (c d : Fin 4) :=
    (((coordinateProjection c).hasFDerivAt (x := x)).mul
      ((coordinateProjection d).hasFDerivAt (x := x))).const_mul
      (normalMetricHessian R a b c d)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun d _ => h c d))
  have hf := (hasFDerivAt_const (metric a b) x).add (hs.const_mul (1 / 2 : ℝ))
  convert hf using 1
  · funext y
    simp only [normalMetricPolynomial, coordinateProjection, Pi.mul_apply,
      ContinuousLinearMap.proj_apply]
    congr 2
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  · simp only [zero_add]
    rfl

theorem normalMetricPolynomial_fderiv (R : curvatureSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) :
    fderiv ℝ (fun y => normalMetricPolynomial R y a b) x =
      normalMetricDerivative R x a b :=
  (normalMetricPolynomial_hasFDerivAt R x a b).fderiv

theorem normalMetricDerivative_at_zero (R : curvatureSpace) (a b : Fin 4) :
    normalMetricDerivative R 0 a b = 0 := by
  simp [normalMetricDerivative]

theorem normalMetricPolynomial_first_derivative_zero (R : curvatureSpace) (a b : Fin 4) :
    fderiv ℝ (fun x => normalMetricPolynomial R x a b) 0 = 0 := by
  rw [normalMetricPolynomial_fderiv, normalMetricDerivative_at_zero]

#print axioms normalMetricPolynomial_hasFDerivAt
#print axioms normalMetricPolynomial_fderiv
#print axioms normalMetricDerivative_at_zero
#print axioms normalMetricPolynomial_first_derivative_zero
end
end AASCSemanticExhaustion
