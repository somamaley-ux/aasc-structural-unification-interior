import WickPoincarePairTransport
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open scoped BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickComplexMatrix : NativeRealMatrix →+* Matrix (Fin 4) (Fin 4) ℂ :=
  Complex.ofRealHom.mapMatrix

theorem wick_complex_matrix_transpose (B : NativeRealMatrix) :
    wickComplexMatrix B.transpose=(wickComplexMatrix B).transpose := rfl

theorem wick_density_contraction_trace (G : NativeRealMatrix) (D : Matrix (Fin 4) (Fin 4) ℂ) :
    (∑ i,∑ j,(G i j : ℂ)*D i j)=Matrix.trace (wickComplexMatrix G*D.transpose) := rfl

theorem wick_trace_congruence_cancellation (A B X D : Matrix (Fin 4) (Fin 4) ℂ)
    (right : A*B=1) :
    Matrix.trace ((B*X*B.transpose)*(A.transpose*D*A).transpose)=Matrix.trace (X*D.transpose) := by
  have trans : B.transpose*A.transpose=1 := by
    rw [← Matrix.transpose_mul, right, Matrix.transpose_one]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B.transpose A.transpose, trans, Matrix.one_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  rw [← Matrix.mul_assoc A B, right, Matrix.one_mul]

theorem wick_quantum_density_congruence (B G : NativeRealMatrix) (detB : B.det=1)
    (D : Matrix (Fin 4) (Fin 4) ℂ) (M : ℂ) :
    wickQuantumActionDensity (B.transpose*G*B)
      ((wickComplexMatrix B).transpose*D*wickComplexMatrix B) M =
      wickQuantumActionDensity G D M := by
  have unit : IsUnit B.det := by rw [detB]; exact isUnit_one
  have right : wickComplexMatrix B * wickComplexMatrix B⁻¹=1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv B unit, map_one]
  have volume : nativeRealClockVolume (B.transpose*G*B)=nativeRealClockVolume G := by
    simp only [nativeRealClockVolume, Matrix.det_mul, Matrix.det_transpose, detB, one_mul, mul_one]
  have inverse : wickComplexMatrix (B.transpose*G*B)⁻¹ =
      wickComplexMatrix B⁻¹ * wickComplexMatrix G⁻¹ * (wickComplexMatrix B⁻¹).transpose := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv,
      map_mul, map_mul, wick_complex_matrix_transpose, Matrix.mul_assoc]
  unfold wickQuantumActionDensity
  rw [volume, wick_density_contraction_trace, wick_density_contraction_trace,
    inverse, wick_trace_congruence_cancellation _ _ _ _ right]

end AASCKleinGordon
