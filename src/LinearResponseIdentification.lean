import RicciSemanticOperators
import SemanticFirstCurvature

namespace AASCSemanticExhaustion
noncomputable section

def responseIndex (o : Fin 10) (j : Fin 20) : Fin 200 :=
  ⟨o.val * 20 + j.val, by omega⟩

theorem response_vector_entry (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (o : Fin 10) (j : Fin 20) :
    responseVector F (responseIndex o j) = responseCoefficient F o j := by
  unfold responseVector responseIndex
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

theorem responseCoefficient_add (F G : curvatureSpace →ₗ[ℝ] Tensor2)
    (o : Fin 10) (j : Fin 20) :
    responseCoefficient (F + G) o j = responseCoefficient F o j + responseCoefficient G o j := by
  simp [responseCoefficient, responseCoordinateMap, map_add]

theorem responseCoefficient_smul (r : ℝ) (F : curvatureSpace →ₗ[ℝ] Tensor2)
    (o : Fin 10) (j : Fin 20) :
    responseCoefficient (r • F) o j = r * responseCoefficient F o j := by
  simp [responseCoefficient, responseCoordinateMap, map_smul]

theorem symmetric_response_coefficient_injective
    (F G : curvatureSpace →ₗ[ℝ] Tensor2)
    (sF : TensorSymmetric F) (sG : TensorSymmetric G)
    (h : ∀ o j, responseCoefficient F o j = responseCoefficient G o j) : F = G := by
  apply LinearMap.ext
  intro R
  rw [arbitrary_linear_response_reconstruction F sF R,
    arbitrary_linear_response_reconstruction G sG R]
  simp_rw [h]

/-- Identification of the certificate's vectors with actual contractions.
The certificate equations are an explicit intermediate premise here; their
derivation from original covariance is a separate theorem. -/
theorem linear_response_from_coefficient_equations
    (F : curvatureSpace →ₗ[ℝ] Tensor2) (symmetric : TensorSymmetric F)
    (equations : ∀ i : Fin 198, commutantEquation i (responseVector F) = 0) :
    F = (responseVector F 199 - responseVector F 194) • ricciResponse +
      (responseVector F 194 / 2) • scalarMetricResponse := by
  let a := responseVector F 199 - responseVector F 194
  let b := responseVector F 194 / 2
  let G := a • ricciResponse + b • scalarMetricResponse
  have sG : TensorSymmetric G := by
    intro R i j
    change a * ricciResponse R i j + b * scalarMetricResponse R i j =
      a * ricciResponse R j i + b * scalarMetricResponse R j i
    rw [ricciResponse_symmetric R i j, scalarMetricResponse_symmetric R i j]
  apply symmetric_response_coefficient_injective F G symmetric sG
  intro o j
  have h := commutant_kernel_reconstruction (responseVector F) equations (responseIndex o j)
  have r := ricci_response_vector (responseIndex o j)
  have s := scalar_metric_response_vector (responseIndex o j)
  rw [response_vector_entry] at h r s
  change responseCoefficient F o j = responseCoefficient G o j
  dsimp only [G]
  rw [responseCoefficient_add, responseCoefficient_smul, responseCoefficient_smul, r, s, h]
  dsimp only [a, b]
  ring

theorem contraction_response_coefficients_unique (a b c a' b' c' : ℝ)
    (h : ∀ R : curvatureSpace,
      a • ricciResponse R + b • scalarMetricResponse R + c • metric =
        a' • ricciResponse R + b' • scalarMetricResponse R + c' • metric) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hz := congrArg (fun B : Tensor2 => B 0 0) (h 0)
  simp only [map_zero, smul_zero, zero_add, add_zero] at hz
  change c * (-1) = c' * (-1) at hz
  have cc : c = c' := by linarith
  have hm : a • ricciResponse + b • scalarMetricResponse =
      a' • ricciResponse + b' • scalarMetricResponse := by
    apply LinearMap.ext
    intro R
    have hr := h R
    rw [cc] at hr
    exact add_right_cancel hr
  have h194 := congrArg (fun F : curvatureSpace →ₗ[ℝ] Tensor2 => responseCoefficient F 9 14) hm
  have h199 := congrArg (fun F : curvatureSpace →ₗ[ℝ] Tensor2 => responseCoefficient F 9 19) hm
  simp only [responseCoefficient_add, responseCoefficient_smul] at h194 h199
  have r194 := ricci_response_vector 194
  have s194 := scalar_metric_response_vector 194
  have r199 := ricci_response_vector 199
  have s199 := scalar_metric_response_vector 199
  norm_num [commutantKernelU, commutantKernelV] at s194 s199
  change responseCoefficient ricciResponse 9 14 = 0 at r194
  change responseCoefficient scalarMetricResponse 9 14 = 2 at s194
  change responseCoefficient ricciResponse 9 19 = 1 at r199
  change responseCoefficient scalarMetricResponse 9 19 = 2 at s199
  rw [r194, s194] at h194
  rw [r199, s199] at h199
  exact ⟨by linarith, by linarith, cc⟩

#print axioms response_vector_entry
#print axioms responseCoefficient_add
#print axioms responseCoefficient_smul
#print axioms symmetric_response_coefficient_injective
#print axioms linear_response_from_coefficient_equations
#print axioms contraction_response_coefficients_unique
end
end AASCSemanticExhaustion
