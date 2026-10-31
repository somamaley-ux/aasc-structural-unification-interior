import CurvatureTransportDefinitions
import SymmetricTensorCoordinates
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 4096
def outputGeneratorMatrix (g : Fin 7) (i j : Fin 10) : ℝ :=
  match g.val, i.val, j.val with
  | 0, 0, 0 => 1
  | 0, 1, 1 => -1
  | 0, 2, 2 => -1
  | 0, 3, 3 => -1
  | 0, 4, 4 => 1
  | 0, 5, 5 => 1
  | 0, 6, 6 => 1
  | 0, 7, 7 => 1
  | 0, 8, 8 => 1
  | 0, 9, 9 => 1
  | 1, 0, 0 => 1
  | 1, 1, 1 => -1
  | 1, 2, 2 => 1
  | 1, 3, 3 => 1
  | 1, 4, 4 => 1
  | 1, 5, 5 => -1
  | 1, 6, 6 => -1
  | 1, 7, 7 => 1
  | 1, 8, 8 => 1
  | 1, 9, 9 => 1
  | 2, 0, 0 => 1
  | 2, 1, 1 => 1
  | 2, 2, 2 => -1
  | 2, 3, 3 => 1
  | 2, 4, 4 => 1
  | 2, 5, 5 => -1
  | 2, 6, 6 => 1
  | 2, 7, 7 => 1
  | 2, 8, 8 => -1
  | 2, 9, 9 => 1
  | 3, 0, 0 => 1
  | 3, 1, 1 => 1
  | 3, 2, 2 => 1
  | 3, 3, 3 => -1
  | 3, 4, 4 => 1
  | 3, 5, 5 => 1
  | 3, 6, 6 => -1
  | 3, 7, 7 => 1
  | 3, 8, 8 => -1
  | 3, 9, 9 => 1
  | 4, 0, 0 => 1
  | 4, 1, 2 => 1
  | 4, 2, 1 => 1
  | 4, 3, 3 => 1
  | 4, 4, 7 => 1
  | 4, 5, 5 => 1
  | 4, 6, 8 => 1
  | 4, 7, 4 => 1
  | 4, 8, 6 => 1
  | 4, 9, 9 => 1
  | 5, 0, 0 => 1
  | 5, 1, 3 => 1
  | 5, 2, 2 => 1
  | 5, 3, 1 => 1
  | 5, 4, 9 => 1
  | 5, 5, 8 => 1
  | 5, 6, 6 => 1
  | 5, 7, 7 => 1
  | 5, 8, 5 => 1
  | 5, 9, 4 => 1
  | 6, 0, 0 => (25 / 16 : ℝ)
  | 6, 0, 1 => (15 / 8 : ℝ)
  | 6, 0, 4 => (9 / 16 : ℝ)
  | 6, 1, 0 => (15 / 16 : ℝ)
  | 6, 1, 1 => (17 / 8 : ℝ)
  | 6, 1, 4 => (15 / 16 : ℝ)
  | 6, 2, 2 => (5 / 4 : ℝ)
  | 6, 2, 5 => (3 / 4 : ℝ)
  | 6, 3, 3 => (5 / 4 : ℝ)
  | 6, 3, 6 => (3 / 4 : ℝ)
  | 6, 4, 0 => (9 / 16 : ℝ)
  | 6, 4, 1 => (15 / 8 : ℝ)
  | 6, 4, 4 => (25 / 16 : ℝ)
  | 6, 5, 2 => (3 / 4 : ℝ)
  | 6, 5, 5 => (5 / 4 : ℝ)
  | 6, 6, 3 => (3 / 4 : ℝ)
  | 6, 6, 6 => (5 / 4 : ℝ)
  | 6, 7, 7 => 1
  | 6, 8, 8 => 1
  | 6, 9, 9 => 1
  | _, _, _ => 0

def outputTransportExplicit (g : Fin 7) (x : Fin 10 → ℝ) (i : Fin 10) : ℝ :=
  match g.val, i.val with
  | 0, 0 => (1) * x 0
  | 0, 1 => (-1) * x 1
  | 0, 2 => (-1) * x 2
  | 0, 3 => (-1) * x 3
  | 0, 4 => (1) * x 4
  | 0, 5 => (1) * x 5
  | 0, 6 => (1) * x 6
  | 0, 7 => (1) * x 7
  | 0, 8 => (1) * x 8
  | 0, 9 => (1) * x 9
  | 1, 0 => (1) * x 0
  | 1, 1 => (-1) * x 1
  | 1, 2 => (1) * x 2
  | 1, 3 => (1) * x 3
  | 1, 4 => (1) * x 4
  | 1, 5 => (-1) * x 5
  | 1, 6 => (-1) * x 6
  | 1, 7 => (1) * x 7
  | 1, 8 => (1) * x 8
  | 1, 9 => (1) * x 9
  | 2, 0 => (1) * x 0
  | 2, 1 => (1) * x 1
  | 2, 2 => (-1) * x 2
  | 2, 3 => (1) * x 3
  | 2, 4 => (1) * x 4
  | 2, 5 => (-1) * x 5
  | 2, 6 => (1) * x 6
  | 2, 7 => (1) * x 7
  | 2, 8 => (-1) * x 8
  | 2, 9 => (1) * x 9
  | 3, 0 => (1) * x 0
  | 3, 1 => (1) * x 1
  | 3, 2 => (1) * x 2
  | 3, 3 => (-1) * x 3
  | 3, 4 => (1) * x 4
  | 3, 5 => (1) * x 5
  | 3, 6 => (-1) * x 6
  | 3, 7 => (1) * x 7
  | 3, 8 => (-1) * x 8
  | 3, 9 => (1) * x 9
  | 4, 0 => (1) * x 0
  | 4, 1 => (1) * x 2
  | 4, 2 => (1) * x 1
  | 4, 3 => (1) * x 3
  | 4, 4 => (1) * x 7
  | 4, 5 => (1) * x 5
  | 4, 6 => (1) * x 8
  | 4, 7 => (1) * x 4
  | 4, 8 => (1) * x 6
  | 4, 9 => (1) * x 9
  | 5, 0 => (1) * x 0
  | 5, 1 => (1) * x 3
  | 5, 2 => (1) * x 2
  | 5, 3 => (1) * x 1
  | 5, 4 => (1) * x 9
  | 5, 5 => (1) * x 8
  | 5, 6 => (1) * x 6
  | 5, 7 => (1) * x 7
  | 5, 8 => (1) * x 5
  | 5, 9 => (1) * x 4
  | 6, 0 => ((25 / 16 : ℝ)) * x 0 + ((15 / 8 : ℝ)) * x 1 + ((9 / 16 : ℝ)) * x 4
  | 6, 1 => ((15 / 16 : ℝ)) * x 0 + ((17 / 8 : ℝ)) * x 1 + ((15 / 16 : ℝ)) * x 4
  | 6, 2 => ((5 / 4 : ℝ)) * x 2 + ((3 / 4 : ℝ)) * x 5
  | 6, 3 => ((5 / 4 : ℝ)) * x 3 + ((3 / 4 : ℝ)) * x 6
  | 6, 4 => ((9 / 16 : ℝ)) * x 0 + ((15 / 8 : ℝ)) * x 1 + ((25 / 16 : ℝ)) * x 4
  | 6, 5 => ((3 / 4 : ℝ)) * x 2 + ((5 / 4 : ℝ)) * x 5
  | 6, 6 => ((3 / 4 : ℝ)) * x 3 + ((5 / 4 : ℝ)) * x 6
  | 6, 7 => (1) * x 7
  | 6, 8 => (1) * x 8
  | 6, 9 => (1) * x 9
  | _, _ => 0

theorem output_generator_transport (g : Fin 7) (x : Fin 10 → ℝ) :
    (comparisonGenerator g).forward.transpose * tensorEncodeLinear x *
      (comparisonGenerator g).forward = tensorEncodeLinear (outputTransportExplicit g x) := by
  ext a b
  fin_cases g <;> fin_cases a <;> fin_cases b <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four] <;>
    norm_num [comparisonGenerator, flipComparison, flipMatrix,
      swap12Comparison, swap13Comparison, boostComparison, swap12Matrix,
      swap13Matrix, boostMatrix, tensorEncodeLinear, tensorEncode, outputTransportExplicit,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_four] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num <;> ring

#print axioms output_generator_transport
end
end AASCSemanticExhaustion
