import C3NormalCurvatureDerivative

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Double contraction of the independent differential Bianchi identity.
Weights may have either sign; no positive-definite metric is assumed. -/
theorem contracted_bianchi_algebra (w : Fin 4 → ℝ) (K : Fin 4 → Tensor4)
    (skewFirst : ∀ e a b c d, K e a b c d = -K e b a c d)
    (skewLast : ∀ e a b c d, K e a b c d = -K e a b d c)
    (bianchi : ∀ a b c d e, K e a b c d + K c a b d e + K d a b e c = 0) (b : Fin 4) :
    (∑ a : Fin 4, ∑ i : Fin 4, w a * w i * K a i a i b) =
      (1 / 2 : ℝ) * (∑ a : Fin 4, ∑ i : Fin 4, w a * w i * K b i a i a) := by
  have hs : (∑ a : Fin 4, ∑ i : Fin 4,
      w a * w i * (K a i a i b + K i i a b a + K b i a a i)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro i _
    rw [bianchi i a i b a, mul_zero]
  have hsecond : (∑ a : Fin 4, ∑ i : Fin 4, w a * w i * K i i a b a) =
      ∑ a : Fin 4, ∑ i : Fin 4, w a * w i * K a i a i b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    rw [skewFirst a a i b i, skewLast a i a b i]
    ring
  have hthird : (∑ a : Fin 4, ∑ i : Fin 4, w a * w i * K b i a a i) =
      -(∑ a : Fin 4, ∑ i : Fin 4, w a * w i * K b i a i a) := by
    calc
      _ = ∑ a : Fin 4, ∑ i : Fin 4, -(w a * w i * K b i a i a) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro i _
        rw [skewLast b i a a i]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [hsecond, hthird] at hs
  linarith

#print axioms contracted_bianchi_algebra
end
end AASCSemanticExhaustion
