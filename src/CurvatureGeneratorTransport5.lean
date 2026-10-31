import CurvatureTransportDefinitions
import FiniteSumTwenty
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 2048

theorem curvature_coordinates_explicit_5 (x : Fin 20 → ℝ) :
    curvatureCoordinateTransport 5 x = curvatureTransportExplicit 5 x := by
  funext i
  unfold curvatureCoordinateTransport
  rw [sum_fin_twenty]
  fin_cases i <;>
    norm_num [curvatureCoordinateTransport, curvatureGeneratorMatrix,
      curvatureTransportExplicit] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 2048 in
theorem curvature_generator_transport_5 (x : Fin 20 → ℝ) :
    pullbackFour (comparisonGenerator 5).forward (curvatureEncode x) =
      curvatureEncode (curvatureCoordinateTransport 5 x) := by
  funext a b c d
  rw [curvature_coordinates_explicit_5]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [pullbackFour, Fin.sum_univ_four] <;>
    norm_num [comparisonGenerator, flipComparison, flipMatrix,
      swap12Comparison, swap13Comparison, boostComparison, swap12Matrix,
      swap13Matrix, boostMatrix,
      Matrix.diagonal_apply, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff] <;>
    norm_num [curvatureEncode, curvatureTransportExplicit] <;> ring
#print axioms curvature_generator_transport_5

end
end AASCSemanticExhaustion
