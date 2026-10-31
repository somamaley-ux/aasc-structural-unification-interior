import NormalMetricSecondDerivatives

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def quadraticPolynomial (Q : Tensor2) (x : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ c : Fin 4, ∑ d : Fin 4, Q c d * x c * x d

def quadraticDerivative (Q : Tensor2) (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ c : Fin 4, ∑ d : Fin 4,
    Q c d • (x c • coordinateProjection d + x d • coordinateProjection c)

def quadraticSecondDerivative (Q : Tensor2) (v : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ c : Fin 4, ∑ d : Fin 4,
    Q c d • (v d • coordinateProjection c + v c • coordinateProjection d)

theorem quadraticPolynomial_hasFDerivAt (Q : Tensor2) (x : Fin 4 → ℝ) :
    HasFDerivAt (quadraticPolynomial Q) (quadraticDerivative Q x) x := by
  have h (c d : Fin 4) :=
    (((coordinateProjection c).hasFDerivAt (x := x)).mul
      ((coordinateProjection d).hasFDerivAt (x := x))).const_mul (Q c d)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun d _ => h c d))
  convert hs.const_mul (1 / 2 : ℝ) using 1
  · funext y
    simp only [quadraticPolynomial, coordinateProjection, Pi.mul_apply, ContinuousLinearMap.proj_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
theorem quadraticPolynomial_fderiv (Q : Tensor2) (x : Fin 4 → ℝ) :
    fderiv ℝ (quadraticPolynomial Q) x = quadraticDerivative Q x :=
  (quadraticPolynomial_hasFDerivAt Q x).fderiv

theorem quadraticDerivative_eval_linear (Q : Tensor2) (v : Fin 4 → ℝ) :
    (fun x => quadraticDerivative Q x v) = quadraticSecondDerivative Q v := by
  funext x
  simp [quadraticDerivative, quadraticSecondDerivative, coordinateProjection, mul_comm]

theorem quadraticSecondDerivative_basis (Q : Tensor2) (c d : Fin 4) :
    quadraticSecondDerivative Q (Pi.single c 1) (Pi.single d 1) =
      (1 / 2 : ℝ) * (Q d c + Q c d) := by
  simp [quadraticSecondDerivative, coordinateProjection, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, ite_mul, mul_ite]

theorem quadraticPolynomial_second_derivative (Q : Tensor2) (c d : Fin 4) :
    fderiv ℝ (fun x => fderiv ℝ (quadraticPolynomial Q) x (Pi.single c 1)) 0 (Pi.single d 1) =
      (1 / 2 : ℝ) * (Q d c + Q c d) := by
  simp_rw [quadraticPolynomial_fderiv]
  rw [quadraticDerivative_eval_linear]
  rw [(quadraticSecondDerivative Q (Pi.single c 1)).hasFDerivAt.fderiv]
  exact quadraticSecondDerivative_basis Q c d

theorem quadraticPolynomial_zero (Q : Tensor2) : quadraticPolynomial Q 0 = 0 := by
  simp [quadraticPolynomial]

theorem quadraticDerivative_zero (Q : Tensor2) : quadraticDerivative Q 0 = 0 := by
  simp [quadraticDerivative]

theorem quadraticPolynomial_smooth (Q : Tensor2) : ContDiff ℝ ⊤ (quadraticPolynomial Q) := by
  unfold quadraticPolynomial
  fun_prop

#print axioms quadraticPolynomial_hasFDerivAt
#print axioms quadraticPolynomial_fderiv
#print axioms quadraticDerivative_eval_linear
#print axioms quadraticSecondDerivative_basis
#print axioms quadraticPolynomial_second_derivative
#print axioms quadraticPolynomial_zero
#print axioms quadraticDerivative_zero
#print axioms quadraticPolynomial_smooth
end
end AASCSemanticExhaustion
