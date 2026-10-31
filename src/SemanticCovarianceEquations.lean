import CurvatureGeneratorActions
import OutputCoordinateAction
import SemanticFirstCurvature
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators

theorem curvature_transport_basis (g : Fin 7) (i j : Fin 20) :
    curvatureCoordinateTransport g (Pi.single j 1) i =
      curvatureGeneratorMatrix g i j := by
  simp [curvatureCoordinateTransport, Pi.single_apply]

/-- The finite action is derived from the original tensor covariance law. -/
theorem response_generator_covariance (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (symmetric : TensorSymmetric F) (covariant : TensorCovariant F)
    (g : Fin 7) (x : Fin 20 → ℝ) :
    responseCoordinateMap F (curvatureCoordinateTransport g x) =
      outputTransportExplicit g (responseCoordinateMap F x) := by
  have h := covariant (comparisonGenerator g) (curvatureEncodeLinear x)
    (curvatureEncodeLinear (curvatureCoordinateTransport g x))
    (curvature_generator_transport g x).symm
  have decomp : tensorEncodeLinear (responseCoordinateMap F x) =
      F (curvatureEncodeLinear x) :=
    tensor_encode_decode (F (curvatureEncodeLinear x)) (symmetric _)
  have h' := congrArg tensorDecode h
  change responseCoordinateMap F (curvatureCoordinateTransport g x) =
    tensorDecode ((comparisonGenerator g).forward.transpose *
      F (curvatureEncodeLinear x) * (comparisonGenerator g).forward) at h'
  rw [← decomp, output_generator_transport] at h'
  change responseCoordinateMap F (curvatureCoordinateTransport g x) =
    tensorDecode (tensorEncode (outputTransportExplicit g (responseCoordinateMap F x))) at h'
  simpa only [tensor_decode_encode] using h'

theorem response_generator_equation (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (symmetric : TensorSymmetric F) (covariant : TensorCovariant F)
    (g : Fin 7) (o : Fin 10) (j : Fin 20) :
    (∑ k : Fin 20, curvatureGeneratorMatrix g k j * responseCoefficient F o k) =
      ∑ k : Fin 10, outputGeneratorMatrix g o k * responseCoefficient F k j := by
  have h := congrFun (response_generator_covariance F symmetric covariant g (Pi.single j 1)) o
  rw [response_coordinate_evaluation] at h
  simp only [curvature_transport_basis] at h
  rw [← output_coordinates_explicit] at h
  exact h

#print axioms curvature_transport_basis
#print axioms response_generator_covariance
#print axioms response_generator_equation
end
end AASCSemanticExhaustion
