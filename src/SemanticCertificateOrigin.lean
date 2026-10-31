import SemanticCovarianceEquations
import RicciSemanticOperators
namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-- Each selected certificate equation is derived from the actual tensor
covariance law on a proved algebraic-curvature basis element. -/
theorem response_vector_equations (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (symmetric : TensorSymmetric F) (covariant : TensorCovariant F) :
    ∀ i : Fin 198, commutantEquation i (responseVector F) = 0 := by
  intro i; fin_cases i
  · have h := response_generator_equation F symmetric covariant 0 0 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 0 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 17) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 1 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 17) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 2 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 17) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 3 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 3 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 4 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 5 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 5 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 6 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 7 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 8 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 0 9 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 0 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 0 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 0 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 0 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 1 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 1 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 1 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 1 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 1 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 2 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 2 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 2 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 2 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 2 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 2 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 2 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 2 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 3 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 3 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 3 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 3 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 3 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 3 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 3 12
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 3 12) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 4 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 4 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 4 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 4 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 17) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 5 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 17) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 6 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 6 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 7 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 7 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 7 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 7 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 8 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 8 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 8 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 8 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 8 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 9 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 9 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 9 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 1 9 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 0 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 0 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 0 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 1 5
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 1 5) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 1 9
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 1 9) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 2 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 4) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 2 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 2 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 3 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 3 3) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 3 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 3 13) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 4 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 4 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 4 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 5 2
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 2) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 5 16
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 5 16) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 6 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 6 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 6 18) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 7 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 7 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 7 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 8 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 8 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 8 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 8 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 8 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 8 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 8 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 8 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 8 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 8 17) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 8 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (2) * (responseCoefficient F 8 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 9 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 7) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 2 9 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-2) * (responseCoefficient F 9 15) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 0 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 0 0)) + (responseCoefficient F 0 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 0 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 0 17)) + (responseCoefficient F 0 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 1 3
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 1 8)) + (-(responseCoefficient F 2 3)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 1 13
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 1 12) + (-(responseCoefficient F 2 13)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 3 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 3 4)) + (responseCoefficient F 3 10) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 4 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 6) + (-(responseCoefficient F 7 0)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 4 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 0) + (-(responseCoefficient F 7 6)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 4 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 11) + (-(responseCoefficient F 7 11)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 4 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 14) + (-(responseCoefficient F 7 14)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 4 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 19) + (-(responseCoefficient F 7 17)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 4 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 17) + (-(responseCoefficient F 7 19)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 6 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 6 2) + (-(responseCoefficient F 8 7)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 6 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 6 16)) + (-(responseCoefficient F 8 15)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 9 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 9 0)) + (responseCoefficient F 9 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 4 9 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 9 17)) + (responseCoefficient F 9 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 0 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 0 0)) + (responseCoefficient F 0 11) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 0 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 0 14)) + (responseCoefficient F 0 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 1 4
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 1 12)) + (-(responseCoefficient F 3 4)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 1 10
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (-(responseCoefficient F 1 8)) + (-(responseCoefficient F 3 10)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 4 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 11) + (-(responseCoefficient F 9 0)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 4 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 6) + (-(responseCoefficient F 9 6)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 4 11
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 0) + (-(responseCoefficient F 9 11)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 4 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 19) + (-(responseCoefficient F 9 14)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 4 17
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 17) + (-(responseCoefficient F 9 17)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 4 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 4 14) + (-(responseCoefficient F 9 19)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 5 7
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 5 1) + (-(responseCoefficient F 8 7)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 5 5 15
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change (responseCoefficient F 5 18) + (-(responseCoefficient F 8 15)) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 0 0
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((-9 / 16 : ℝ)) * (responseCoefficient F 0 0) + ((-15 / 8 : ℝ)) * (responseCoefficient F 1 0) + ((-9 / 16 : ℝ)) * (responseCoefficient F 4 0) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 0 6
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((15 / 16 : ℝ)) * (responseCoefficient F 0 8) + ((9 / 16 : ℝ)) * (responseCoefficient F 0 14) + ((-15 / 8 : ℝ)) * (responseCoefficient F 1 6) + ((-9 / 16 : ℝ)) * (responseCoefficient F 4 6) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 0 8
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((15 / 8 : ℝ)) * (responseCoefficient F 0 6) + ((9 / 16 : ℝ)) * (responseCoefficient F 0 8) + ((15 / 8 : ℝ)) * (responseCoefficient F 0 14) + ((-15 / 8 : ℝ)) * (responseCoefficient F 1 8) + ((-9 / 16 : ℝ)) * (responseCoefficient F 4 8) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 0 14
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((9 / 16 : ℝ)) * (responseCoefficient F 0 6) + ((15 / 16 : ℝ)) * (responseCoefficient F 0 8) + ((-15 / 8 : ℝ)) * (responseCoefficient F 1 14) + ((-9 / 16 : ℝ)) * (responseCoefficient F 4 14) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 0 19
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((-9 / 16 : ℝ)) * (responseCoefficient F 0 19) + ((-15 / 8 : ℝ)) * (responseCoefficient F 1 19) + ((-9 / 16 : ℝ)) * (responseCoefficient F 4 19) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 2 1
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((3 / 4 : ℝ)) * (responseCoefficient F 2 3) + ((-3 / 4 : ℝ)) * (responseCoefficient F 5 1) = 0
    first | linear_combination h | linarith only [h]
  · have h := response_generator_equation F symmetric covariant 6 2 18
    simp only [sum_fin_twenty, sum_fin_ten] at h
    norm_num [curvatureGeneratorMatrix, outputGeneratorMatrix] at h
    change ((3 / 4 : ℝ)) * (responseCoefficient F 2 13) + ((-3 / 4 : ℝ)) * (responseCoefficient F 5 18) = 0
    first | linear_combination h | linarith only [h]

#print axioms response_vector_equations
end
end AASCSemanticExhaustion
