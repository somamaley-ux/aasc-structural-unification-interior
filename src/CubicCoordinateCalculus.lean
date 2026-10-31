import QuadraticCoordinateCalculus

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

abbrev CubicArray := Fin 4 → Fin 4 → Fin 4 → ℝ

def SymmetricCubicArray (C : CubicArray) : Prop :=
  (∀ a b c, C a b c = C b a c) ∧ (∀ a b c, C a b c = C a c b)

def cubicPolynomial (C : CubicArray) (x : Fin 4 → ℝ) : ℝ :=
  (1 / 6 : ℝ) * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, C a b c * x a * x b * x c

def cubicDerivative (C : CubicArray) (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  (1 / 6 : ℝ) • ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
    C a b c • ((x b * x c) • coordinateProjection a +
      (x a * x c) • coordinateProjection b + (x a * x b) • coordinateProjection c)

theorem cubicPolynomial_hasFDerivAt (C : CubicArray) (x : Fin 4 → ℝ) :
    HasFDerivAt (cubicPolynomial C) (cubicDerivative C x) x := by
  have h (a b c : Fin 4) :=
    ((((coordinateProjection a).hasFDerivAt (x := x)).mul
      ((coordinateProjection b).hasFDerivAt (x := x))).mul
      ((coordinateProjection c).hasFDerivAt (x := x))).const_mul (C a b c)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ => h a b c)))
  convert hs.const_mul (1 / 6 : ℝ) using 1
  · funext y
    simp only [cubicPolynomial, coordinateProjection, Pi.mul_apply, ContinuousLinearMap.proj_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  · ext v
    simp only [cubicDerivative, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.add_apply, smul_eq_mul, coordinateProjection, Pi.mul_apply,
      ContinuousLinearMap.proj_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring

theorem cubicPolynomial_fderiv (C : CubicArray) (x : Fin 4 → ℝ) :
    fderiv ℝ (cubicPolynomial C) x = cubicDerivative C x :=
  (cubicPolynomial_hasFDerivAt C x).fderiv

theorem cubicPolynomial_zero (C : CubicArray) : cubicPolynomial C 0 = 0 := by
  simp [cubicPolynomial]

theorem cubicDerivative_zero (C : CubicArray) : cubicDerivative C 0 = 0 := by
  simp [cubicDerivative]

theorem cubicPolynomial_smooth (C : CubicArray) : ContDiff ℝ ⊤ (cubicPolynomial C) := by
  unfold cubicPolynomial
  fun_prop

theorem symmetric_cubic_derivative_basis (C : CubicArray) (symmetric : SymmetricCubicArray C)
    (x : Fin 4 → ℝ) (a : Fin 4) :
    cubicDerivative C x (Pi.single a 1) = quadraticPolynomial (fun b c => C a b c) x := by
  have hm (i k : Fin 4) : C i a k = C a i k := symmetric.1 i a k
  have hl (i j : Fin 4) : C i j a = C a i j := by
    rw [symmetric.2 i j a, symmetric.1 i a j]
  simp [cubicDerivative, coordinateProjection, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, mul_ite]
  simp_rw [hm, hl]
  unfold quadraticPolynomial
  ring

#print axioms cubicPolynomial_hasFDerivAt
#print axioms cubicPolynomial_fderiv
#print axioms cubicPolynomial_zero
#print axioms cubicDerivative_zero
#print axioms cubicPolynomial_smooth
#print axioms symmetric_cubic_derivative_basis
end
end AASCSemanticExhaustion
