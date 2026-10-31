import CoordinateRicciDerivative
import Mathlib.LinearAlgebra.Matrix.Trace

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

def matrixContractionLinear (G : Tensor2) : Tensor2 →ₗ[ℝ] ℝ where
  toFun M := ∑ i : Fin 4, ∑ j : Fin 4, G i j * M i j
  map_add' M N := by simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r M := by
    simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem matrixContraction_eq_trace (G M : Tensor2) :
    matrixContractionLinear G M = Matrix.trace (G.transpose * M) := by
  simp only [matrixContractionLinear, LinearMap.coe_mk, AddHom.coe_mk, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem matrixContraction_pullback (H A M : Tensor2) :
    matrixContractionLinear H (A.transpose * M * A) =
      matrixContractionLinear (A * H * A.transpose) M := by
  rw [matrixContraction_eq_trace, matrixContraction_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = Matrix.trace ((H.transpose * A.transpose * M) * A) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (A * (H.transpose * A.transpose * M)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

def curvatureMatrixSlice (R : Tensor4) (a b : Fin 4) : Tensor2 := fun i j => R i a j b

def tensorRicci (G : Tensor2) (R : Tensor4) : Tensor2 := fun a b => matrixContractionLinear G (curvatureMatrixSlice R a b)

def weightedCurvatureSlice (A : Tensor2) (R : Tensor4) (a b : Fin 4) : Tensor2 :=
  ∑ j : Fin 4, ∑ l : Fin 4, (A j a * A l b) • curvatureMatrixSlice R j l

theorem pullbackFour_matrix_slice (A : Tensor2) (R : Tensor4) (a b : Fin 4) :
    curvatureMatrixSlice (pullbackFour A R) a b = A.transpose * weightedCurvatureSlice A R a b * A := by
  ext u v
  rw [← matrix_pullback_double_sum]
  simp only [curvatureMatrixSlice, pullbackFour_flat, weightedCurvatureSlice,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem tensorRicci_pullback (A H G : Tensor2) (R : Tensor4)
    (contraction : A * H * A.transpose = G) :
    tensorRicci H (pullbackFour A R) = A.transpose * tensorRicci G R * A := by
  ext a b
  change matrixContractionLinear H (curvatureMatrixSlice (pullbackFour A R) a b) = _
  rw [pullbackFour_matrix_slice, matrixContraction_pullback, contraction]
  simp only [weightedCurvatureSlice, map_sum, map_smul, smul_eq_mul]
  rw [← matrix_pullback_double_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  change (A j a * A l b) * matrixContractionLinear G (curvatureMatrixSlice R j l) =
    A j a * matrixContractionLinear G (curvatureMatrixSlice R j l) * A l b
  ring

theorem ricciResponse_eq_tensorRicci (R : curvatureSpace) : ricciResponse R = tensorRicci metric R := by
  ext a b
  norm_num [ricciResponse, tensorRicci, matrixContractionLinear, curvatureMatrixSlice,
    metric, Matrix.diagonal_apply, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]

theorem scalarCurvatureResponse_eq_contraction (R : curvatureSpace) :
    scalarCurvatureResponse R = matrixContractionLinear metric (ricciResponse R) := by
  norm_num [scalarCurvatureResponse, matrixContractionLinear, metric, Matrix.diagonal_apply,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

#print axioms matrixContraction_eq_trace
#print axioms matrixContraction_pullback
#print axioms pullbackFour_matrix_slice
#print axioms tensorRicci_pullback
#print axioms ricciResponse_eq_tensorRicci
#print axioms scalarCurvatureResponse_eq_contraction
end
end AASCSemanticExhaustion
