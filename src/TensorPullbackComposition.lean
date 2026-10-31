import PointNormalChartTransition

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def tensorPullbackAxis0 (A : Tensor2) (R : Tensor4) (a b c d : Fin 4) : ℝ :=
  ∑ i : Fin 4, A i a * R i b c d

def tensorPullbackAxis1 (A : Tensor2) (R : Tensor4) (a b c d : Fin 4) : ℝ :=
  ∑ i : Fin 4, A i b * R a i c d

def tensorPullbackAxis2 (A : Tensor2) (R : Tensor4) (a b c d : Fin 4) : ℝ :=
  ∑ i : Fin 4, A i c * R a b i d

def tensorPullbackAxis3 (A : Tensor2) (R : Tensor4) (a b c d : Fin 4) : ℝ :=
  ∑ i : Fin 4, A i d * R a b c i

theorem tensorPullbackAxis0_comp (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis0 B (tensorPullbackAxis0 A R) = tensorPullbackAxis0 (A * B) R := by
  funext a b c d
  simp only [tensorPullbackAxis0, Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis1_comp (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis1 B (tensorPullbackAxis1 A R) = tensorPullbackAxis1 (A * B) R := by
  funext a b c d
  simp only [tensorPullbackAxis1, Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis2_comp (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis2 B (tensorPullbackAxis2 A R) = tensorPullbackAxis2 (A * B) R := by
  funext a b c d
  simp only [tensorPullbackAxis2, Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis3_comp (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis3 B (tensorPullbackAxis3 A R) = tensorPullbackAxis3 (A * B) R := by
  funext a b c d
  simp only [tensorPullbackAxis3, Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis1_0_comm (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis1 A (tensorPullbackAxis0 B R) =
      tensorPullbackAxis0 B (tensorPullbackAxis1 A R) := by
  funext a b c d
  simp only [tensorPullbackAxis1, tensorPullbackAxis0, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis2_0_comm (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis2 A (tensorPullbackAxis0 B R) =
      tensorPullbackAxis0 B (tensorPullbackAxis2 A R) := by
  funext a b c d
  simp only [tensorPullbackAxis2, tensorPullbackAxis0, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis2_1_comm (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis2 A (tensorPullbackAxis1 B R) =
      tensorPullbackAxis1 B (tensorPullbackAxis2 A R) := by
  funext a b c d
  simp only [tensorPullbackAxis2, tensorPullbackAxis1, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis3_0_comm (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis3 A (tensorPullbackAxis0 B R) =
      tensorPullbackAxis0 B (tensorPullbackAxis3 A R) := by
  funext a b c d
  simp only [tensorPullbackAxis3, tensorPullbackAxis0, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis3_1_comm (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis3 A (tensorPullbackAxis1 B R) =
      tensorPullbackAxis1 B (tensorPullbackAxis3 A R) := by
  funext a b c d
  simp only [tensorPullbackAxis3, tensorPullbackAxis1, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorPullbackAxis3_2_comm (A B : Tensor2) (R : Tensor4) :
    tensorPullbackAxis3 A (tensorPullbackAxis2 B R) =
      tensorPullbackAxis2 B (tensorPullbackAxis3 A R) := by
  funext a b c d
  simp only [tensorPullbackAxis3, tensorPullbackAxis2, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pullbackFour_eq_axes (A : Tensor2) (R : Tensor4) :
    pullbackFour A R = tensorPullbackAxis0 A (tensorPullbackAxis1 A
      (tensorPullbackAxis2 A (tensorPullbackAxis3 A R))) := rfl

theorem pullbackFour_comp (A B : Tensor2) (R : Tensor4) :
    pullbackFour B (pullbackFour A R) = pullbackFour (A * B) R := by
  simp only [pullbackFour_eq_axes]
  rw [tensorPullbackAxis3_0_comm, tensorPullbackAxis2_0_comm, tensorPullbackAxis1_0_comm,
    tensorPullbackAxis0_comp, tensorPullbackAxis3_1_comm, tensorPullbackAxis2_1_comm,
    tensorPullbackAxis1_comp, tensorPullbackAxis3_2_comm, tensorPullbackAxis2_comp,
    tensorPullbackAxis3_comp]

theorem pullbackFour_identity (R : Tensor4) : pullbackFour 1 R = R := by
  funext a b c d
  simp [pullbackFour, Matrix.one_apply, ite_mul]
#print axioms tensorPullbackAxis0_comp
#print axioms tensorPullbackAxis1_comp
#print axioms tensorPullbackAxis2_comp
#print axioms tensorPullbackAxis3_comp
#print axioms tensorPullbackAxis1_0_comm
#print axioms tensorPullbackAxis2_0_comm
#print axioms tensorPullbackAxis2_1_comm
#print axioms tensorPullbackAxis3_0_comm
#print axioms tensorPullbackAxis3_1_comm
#print axioms tensorPullbackAxis3_2_comm
#print axioms pullbackFour_eq_axes
#print axioms pullbackFour_comp
#print axioms pullbackFour_identity
end
end AASCSemanticExhaustion
