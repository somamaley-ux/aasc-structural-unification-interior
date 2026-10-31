import AlgebraicCurvatureCoordinates
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace AASCSemanticExhaustion

set_option maxHeartbeats 0 in
theorem curvatureEncode_add (x y : Fin 20 → ℝ) :
    curvatureEncode (x + y) = curvatureEncode x + curvatureEncode y := by
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [curvatureEncode] <;> ring

set_option maxHeartbeats 0 in
theorem curvatureEncode_smul (r : ℝ) (x : Fin 20 → ℝ) :
    curvatureEncode (r • x) = r • curvatureEncode x := by
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [curvatureEncode] <;> ring

def curvatureEncodeLinear : (Fin 20 → ℝ) →ₗ[ℝ] curvatureSpace where
  toFun x := ⟨curvatureEncode x, curvatureEncode_mem x⟩
  map_add' x y := Subtype.ext (curvatureEncode_add x y)
  map_smul' r x := Subtype.ext (curvatureEncode_smul r x)

def curvatureDecodeLinear : curvatureSpace →ₗ[ℝ] (Fin 20 → ℝ) where
  toFun := curvatureDecode
  map_add' R S := by funext i; fin_cases i <;> rfl
  map_smul' r R := by funext i; fin_cases i <;> rfl

/-- Exact coordinate equivalence for tensors defined by the original four
curvature laws. This is not an expression class or a completeness assumption. -/
def curvatureCoordinateEquiv : curvatureSpace ≃ₗ[ℝ] (Fin 20 → ℝ) where
  toFun := curvatureDecode
  invFun x := ⟨curvatureEncode x, curvatureEncode_mem x⟩
  left_inv R := Subtype.ext (curvature_encode_decode R)
  right_inv := curvature_decode_encode
  map_add' := curvatureDecodeLinear.map_add
  map_smul' := curvatureDecodeLinear.map_smul

open scoped BigOperators

theorem linear_twenty_coordinates {M : Type*} [AddCommGroup M] [Module ℝ M]
    (F : (Fin 20 → ℝ) →ₗ[ℝ] M) (x : Fin 20 → ℝ) :
    F x = ∑ j : Fin 20, x j • F (Pi.single j 1) := by
  have h := congrArg F ((Pi.basisFun ℝ (Fin 20)).sum_repr x)
  simpa only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr] using h.symm

#print axioms curvatureEncode_add
#print axioms curvatureEncode_smul
#print axioms linear_twenty_coordinates

end AASCSemanticExhaustion
