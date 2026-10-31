import NativeFiniteNeumannInverse
import Mathlib.Data.Matrix.Mul

/-! Actual exterior coefficients and exact degree-two metric inversion. These
are algebraic ingredients of CSP-C 8.1, not a new physical target or a record
whose fields assert the desired inverse. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

variable {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

def nativeBodyMatrixEmbed (H : Matrix ι ι R) : Matrix ι ι A :=
  H.map (algebraMap R A)

def nativeExteriorCoefficientMatrix (ε : A) (H : Matrix ι ι R) : Matrix ι ι A :=
  fun a b => algebraMap R A (H a b)*ε

theorem native_coefficient_entry_product_zero (ε : A) (square_zero : ε*ε=0) (r s : R) :
    (algebraMap R A r*ε)*(algebraMap R A s*ε)=0 := by
  calc
    _=algebraMap R A r*(ε*algebraMap R A s)*ε := by simp only [mul_assoc]
    _=algebraMap R A r*(algebraMap R A s*ε)*ε := by rw [← Algebra.commutes s ε]
    _=(algebraMap R A r*algebraMap R A s)*(ε*ε) := by simp only [mul_assoc]
    _=0 := by rw [square_zero,mul_zero]

theorem native_coefficient_matrix_square_zero (ε : A) (square_zero : ε*ε=0)
    (H : Matrix ι ι R) : (nativeExteriorCoefficientMatrix ε H)^2=0 := by
  rw [pow_two]
  ext a b
  simp only [Matrix.mul_apply,nativeExteriorCoefficientMatrix,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact native_coefficient_entry_product_zero ε square_zero _ _

theorem native_body_matrix_embed_mul (B H : Matrix ι ι R) :
    nativeBodyMatrixEmbed (A := A) (B*H)=nativeBodyMatrixEmbed B*nativeBodyMatrixEmbed H := by
  ext a b
  simp [nativeBodyMatrixEmbed,Matrix.mul_apply,map_sum,map_mul]

theorem native_body_times_exterior_coefficient (B H : Matrix ι ι R) (ε : A) :
    nativeBodyMatrixEmbed B*nativeExteriorCoefficientMatrix ε H=
      nativeExteriorCoefficientMatrix ε (B*H) := by
  ext a b
  simp [nativeBodyMatrixEmbed,nativeExteriorCoefficientMatrix,Matrix.mul_apply,map_sum,
    map_mul,Finset.sum_mul,mul_assoc]

theorem native_coefficient_times_body (H B : Matrix ι ι R) (ε : A) :
    nativeExteriorCoefficientMatrix ε H*nativeBodyMatrixEmbed B=
      nativeExteriorCoefficientMatrix ε (H*B) := by
  ext a b
  simp only [Matrix.mul_apply,nativeExteriorCoefficientMatrix,nativeBodyMatrixEmbed,
    Matrix.map_apply,map_sum,map_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc,← Algebra.commutes (B j b) ε,← mul_assoc]

theorem native_exterior_metric_inverse_degree_two (G B H : Matrix ι ι R)
    (rightBody : G*B=1) (leftBody : B*G=1) (ε : A) (square_zero : ε*ε=0) :
    (nativeBodyMatrixEmbed G+nativeExteriorCoefficientMatrix ε H)*
      (nativeBodyMatrixEmbed B-nativeExteriorCoefficientMatrix ε (B*H*B))=1 ∧
    (nativeBodyMatrixEmbed B-nativeExteriorCoefficientMatrix ε (B*H*B))*
      (nativeBodyMatrixEmbed G+nativeExteriorCoefficientMatrix ε H)=1 := by
  have hG : nativeBodyMatrixEmbed (A := A) G*nativeBodyMatrixEmbed B=1 := by
    rw [← native_body_matrix_embed_mul,rightBody]
    ext a b
    simp [nativeBodyMatrixEmbed,Matrix.one_apply]
  have hB : nativeBodyMatrixEmbed (A := A) B*nativeBodyMatrixEmbed G=1 := by
    rw [← native_body_matrix_embed_mul,leftBody]
    ext a b
    simp [nativeBodyMatrixEmbed,Matrix.one_apply]
  have hn : (nativeBodyMatrixEmbed B*nativeExteriorCoefficientMatrix ε H)^2=0 := by
    rw [native_body_times_exterior_coefficient]
    exact native_coefficient_matrix_square_zero ε square_zero _
  have hf : nativeNilpotentPerturbationInverse (nativeBodyMatrixEmbed B)
      (nativeExteriorCoefficientMatrix ε H) 2=
      nativeBodyMatrixEmbed B-nativeExteriorCoefficientMatrix ε (B*H*B) := by
    rw [native_square_zero_inverse_first_correction,native_body_times_exterior_coefficient,
      native_coefficient_times_body]
  constructor
  · rw [← hf]
    exact native_nilpotent_perturbation_inverse_left _ _ _ 2 hG hB hn
  · rw [← hf]
    exact native_nilpotent_perturbation_inverse_right _ _ _ 2 hG hB hn

theorem native_csp_exterior_metric_inverse_degree_two (N : ℕ) (i j : Fin N)
    (G B H : Matrix (Fin 4) (Fin 4) ℂ) (rightBody : G*B=1) (leftBody : B*G=1) :
    (nativeBodyMatrixEmbed G+nativeExteriorCoefficientMatrix (nativeCSPDegreeTwoCoefficient N i j) H)*
      (nativeBodyMatrixEmbed B-nativeExteriorCoefficientMatrix (nativeCSPDegreeTwoCoefficient N i j) (B*H*B))=1 ∧
    (nativeBodyMatrixEmbed B-nativeExteriorCoefficientMatrix (nativeCSPDegreeTwoCoefficient N i j) (B*H*B))*
      (nativeBodyMatrixEmbed G+nativeExteriorCoefficientMatrix (nativeCSPDegreeTwoCoefficient N i j) H)=1 := by
  apply native_exterior_metric_inverse_degree_two G B H rightBody leftBody
  simpa only [pow_two] using native_csp_degree_two_coefficient_square_zero N i j

#print axioms native_coefficient_entry_product_zero
#print axioms native_coefficient_matrix_square_zero
#print axioms native_body_matrix_embed_mul
#print axioms native_body_times_exterior_coefficient
#print axioms native_coefficient_times_body
#print axioms native_exterior_metric_inverse_degree_two
#print axioms native_csp_exterior_metric_inverse_degree_two
end
end AASCSemanticExhaustion
