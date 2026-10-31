import SemanticResponseCoordinates
import CurvatureCommutantCertificate

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators

/-- Actual inverse-metric contraction in the received diagonal Lorentz fibre. -/
def ricciResponse : curvatureSpace →ₗ[ℝ] Tensor2 where
  toFun R i j := -(R : Tensor4) 0 i 0 j + (R : Tensor4) 1 i 1 j +
    (R : Tensor4) 2 i 2 j + (R : Tensor4) 3 i 3 j
  map_add' R S := by
    ext i j
    simp only [Submodule.coe_add, Pi.add_apply, Matrix.add_apply]
    ring
  map_smul' r R := by
    ext i j
    simp only [Submodule.coe_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def scalarCurvatureResponse : curvatureSpace →ₗ[ℝ] ℝ where
  toFun R := -ricciResponse R 0 0 + ricciResponse R 1 1 +
    ricciResponse R 2 2 + ricciResponse R 3 3
  map_add' R S := by simp only [map_add, Matrix.add_apply]; ring
  map_smul' r R := by simp only [map_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def scalarMetricResponse : curvatureSpace →ₗ[ℝ] Tensor2 where
  toFun R := scalarCurvatureResponse R • metric
  map_add' R S := by simp only [map_add, add_smul]
  map_smul' r R := by simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

theorem ricciResponse_symmetric (R : curvatureSpace) (i j : Fin 4) :
    ricciResponse R i j = ricciResponse R j i := by
  change -(R : Tensor4) 0 i 0 j + (R : Tensor4) 1 i 1 j +
    (R : Tensor4) 2 i 2 j + (R : Tensor4) 3 i 3 j = _
  rw [R.property.2.2.1 0 i 0 j, R.property.2.2.1 1 i 1 j,
    R.property.2.2.1 2 i 2 j, R.property.2.2.1 3 i 3 j]
  rfl

theorem scalarMetricResponse_symmetric (R : curvatureSpace) (i j : Fin 4) :
    scalarMetricResponse R i j = scalarMetricResponse R j i := by
  change scalarCurvatureResponse R * metric i j = scalarCurvatureResponse R * metric j i
  congr 1
  by_cases h : i = j
  · subst j; rfl
  · simp [metric, Matrix.diagonal_apply, h, Ne.symm h]

def responseVector (F : curvatureSpace →ₗ[ℝ] Tensor2) (i : Fin 200) : ℝ :=
  responseCoefficient F ⟨i.val / 20, by omega⟩ ⟨i.val % 20, Nat.mod_lt _ (by omega)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
theorem ricci_response_vector (i : Fin 200) :
    responseVector ricciResponse i = commutantKernelV i := by
  fin_cases i <;>
    norm_num [responseVector, responseCoefficient, responseCoordinateMap,
      tensorDecodeLinear, tensorDecode, ricciResponse, curvatureEncodeLinear,
      curvatureEncode, Pi.single_apply, commutantKernelV] <;>
    simp only [Fin.ext_iff] <;> norm_num

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
theorem scalar_metric_response_vector (i : Fin 200) :
    responseVector scalarMetricResponse i =
      2 * (commutantKernelU i + commutantKernelV i) := by
  fin_cases i <;>
    norm_num [responseVector, responseCoefficient, responseCoordinateMap,
      tensorDecodeLinear, tensorDecode, scalarMetricResponse, scalarCurvatureResponse,
      ricciResponse, curvatureEncodeLinear, curvatureEncode, Pi.single_apply,
      metric, Matrix.diagonal_apply, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, commutantKernelU, commutantKernelV] <;>
    simp only [Fin.ext_iff] <;> norm_num

#print axioms ricciResponse_symmetric
#print axioms scalarMetricResponse_symmetric
#print axioms ricci_response_vector
#print axioms scalar_metric_response_vector
end
end AASCSemanticExhaustion
