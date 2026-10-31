import AlgebraicCurvatureLinear
import SymmetricTensorCoordinates
import Mathlib.Algebra.BigOperators.Pi

/-!
Coordinate completeness for an arbitrary linear operator on the independently
defined algebraic-curvature space. Symmetry is an original output law. No
operator expression, Ricci normal form or completeness field is a premise.
-/

namespace AASCSemanticExhaustion

open scoped BigOperators

def responseCoordinateMap (F : curvatureSpace →ₗ[ℝ] Tensor2) :
    (Fin 20 → ℝ) →ₗ[ℝ] (Fin 10 → ℝ) :=
  tensorDecodeLinear.comp (F.comp curvatureEncodeLinear)

def responseCoefficient (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (o : Fin 10) (j : Fin 20) : ℝ :=
  responseCoordinateMap F (Pi.single j 1) o

theorem response_coordinate_evaluation (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (x : Fin 20 → ℝ) (o : Fin 10) :
    responseCoordinateMap F x o = ∑ j : Fin 20, x j * responseCoefficient F o j := by
  have h := congrArg (fun y : Fin 10 → ℝ => y o)
    (linear_twenty_coordinates (responseCoordinateMap F) x)
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, responseCoefficient] using h

theorem arbitrary_linear_response_reconstruction
    (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (symmetric : ∀ R i j, F R i j = F R j i) (R : curvatureSpace) :
    F R = tensorEncode (fun o =>
      ∑ j : Fin 20, curvatureDecode R j * responseCoefficient F o j) := by
  have hrec : curvatureEncodeLinear (curvatureDecode R) = R :=
    Subtype.ext (curvature_encode_decode R)
  have coords : tensorDecode (F R) =
      (fun o => ∑ j : Fin 20, curvatureDecode R j * responseCoefficient F o j) := by
    funext o
    have h := response_coordinate_evaluation F (curvatureDecode R) o
    change tensorDecode (F (curvatureEncodeLinear (curvatureDecode R))) o = _ at h
    rw [hrec] at h
    exact h
  rw [← coords]
  exact (tensor_encode_decode (F R) (symmetric R)).symm

#print axioms response_coordinate_evaluation
#print axioms arbitrary_linear_response_reconstruction

end AASCSemanticExhaustion
