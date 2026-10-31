import CurvatureTransportDefinitions
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 2048

theorem curvature_generator_diagonal_0 (i j : Fin 20) :
    curvatureGeneratorMatrix 0 i j =
      if i = j then curvatureGeneratorDiagonal 0 i else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem curvature_coordinates_explicit_0 (x : Fin 20 → ℝ) :
    curvatureCoordinateTransport 0 x = curvatureTransportExplicit 0 x := by
  funext i
  unfold curvatureCoordinateTransport
  simp_rw [curvature_generator_diagonal_0]
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  fin_cases i <;> simp [curvatureTransportExplicit, curvatureGeneratorDiagonal]

set_option maxHeartbeats 0 in
set_option maxRecDepth 2048 in
theorem curvature_generator_transport_0 (x : Fin 20 → ℝ) :
    pullbackFour (comparisonGenerator 0).forward (curvatureEncode x) =
      curvatureEncode (curvatureCoordinateTransport 0 x) := by
  funext a b c d
  change pullbackFour (flipComparison 0).forward (curvatureEncode x) a b c d = _
  rw [pullbackFour_flip]
  rw [curvature_coordinates_explicit_0]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [pullbackFour, comparisonGenerator, flipComparison, flipMatrix,
      swap12Comparison, swap13Comparison, boostComparison, swap12Matrix,
      swap13Matrix, boostMatrix, curvatureEncode, curvatureTransportExplicit,
      Matrix.diagonal_apply, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ] <;> ring
#print axioms curvature_generator_transport_0

end
end AASCSemanticExhaustion
