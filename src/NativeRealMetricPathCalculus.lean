import NativeClockMetricActionFirstJet
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Ordinary real metric-path calculus. The finite matrix operator norm is used
only to invoke the proved Banach-algebra inverse theorem; no LF topology is
replaced. Public component derivatives have ordinary real codomain. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators Topology Matrix.Norms.Operator
open Filter

abbrev NativeRealMatrix := Matrix (Fin 4) (Fin 4) ℝ

def nativeRealMatrixEntry (i j : Fin 4) : NativeRealMatrix →L[ℝ] ℝ :=
  ({ toFun:=fun M => M i j
     map_add':=by intros; rfl
     map_smul':=by intros; rfl } : NativeRealMatrix →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem native_real_metric_inverse_path_hasDerivAt (G B H : NativeRealMatrix)
    (hGB : G*B=1) (hBG : B*G=1) :
    HasDerivAt (fun s : ℝ => (G+s • H)⁻¹) (-B*H*B) 0 := by
  let u : NativeRealMatrixˣ:=⟨G,B,hGB,hBG⟩
  have hi:=hasFDerivAt_ringInverse (𝕜:=ℝ) u
  have hp : HasDerivAt (fun s : ℝ => G+s • H) H 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const H).const_add G
  have hi' : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ NativeRealMatrix B B) (G+(0:ℝ) • H) := by
    simpa [u] using hi
  have h:=hi'.comp_hasDerivAt 0 hp
  simpa [u,Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse,
    ContinuousLinearMap.mulLeftRight_apply] using h

theorem native_real_metric_inverse_entry_hasDerivAt (G B H : NativeRealMatrix)
    (hGB : G*B=1) (hBG : B*G=1) (i j : Fin 4) :
    HasDerivAt (fun s : ℝ => (G+s • H)⁻¹ i j) ((-B*H*B) i j) 0 := by
  have h:=(nativeRealMatrixEntry i j).hasFDerivAt.comp_hasDerivAt 0
    (native_real_metric_inverse_path_hasDerivAt G B H hGB hBG)
  exact h

theorem native_real_identity_determinant_path_hasDerivAt (K : NativeRealMatrix) :
    HasDerivAt (fun s : ℝ => (1+s • K).det) (Matrix.trace K) 0 := by
  let P : Polynomial ℝ:=(Matrix.det (1+(Polynomial.X:Polynomial ℝ) • K.map Polynomial.C)).divX.divX
  have hP:=P.hasDerivAt (0:ℝ)
  have ht:=hasDerivAt_id (0:ℝ)
  have h:=((hasDerivAt_const (0:ℝ) (1:ℝ)).add (ht.const_mul (Matrix.trace K))).add
    (hP.mul (ht.pow 2))
  have heq : (fun s : ℝ => (1+s • K).det)=
      (fun s : ℝ => 1+Matrix.trace K*s+P.eval s*s^2) := by
    funext s
    exact Matrix.det_one_add_smul s K
  rw [heq]
  simpa using h

theorem native_real_metric_determinant_path_hasDerivAt (G B H : NativeRealMatrix)
    (hGB : G*B=1) :
    HasDerivAt (fun s : ℝ => (G+s • H).det) (G.det*Matrix.trace (B*H)) 0 := by
  have hf (s : ℝ) : G+s • H=G*(1+s • (B*H)) := by
    rw [mul_add,mul_one,Matrix.mul_smul,← mul_assoc,hGB,one_mul]
  have hd:=(native_real_identity_determinant_path_hasDerivAt (B*H)).const_mul G.det
  simpa only [hf,Matrix.det_mul] using hd

#print axioms native_real_metric_inverse_path_hasDerivAt
#print axioms native_real_metric_inverse_entry_hasDerivAt
#print axioms native_real_identity_determinant_path_hasDerivAt
#print axioms native_real_metric_determinant_path_hasDerivAt
end
end AASCSemanticExhaustion
