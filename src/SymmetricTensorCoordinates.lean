import LorentzInvariantBaseline
import Mathlib.Algebra.Module.LinearMap.Defs

namespace AASCSemanticExhaustion

def tensorEncode (x : Fin 10 → ℝ) (i j : Fin 4) : ℝ :=
  match i.val, j.val with
  | 0, 0 => x 0
  | 0, 1 | 1, 0 => x 1
  | 0, 2 | 2, 0 => x 2
  | 0, 3 | 3, 0 => x 3
  | 1, 1 => x 4
  | 1, 2 | 2, 1 => x 5
  | 1, 3 | 3, 1 => x 6
  | 2, 2 => x 7
  | 2, 3 | 3, 2 => x 8
  | _, _ => x 9

def tensorDecode (B : Tensor2) (i : Fin 10) : ℝ :=
  match i.val with
  | 0 => B 0 0
  | 1 => B 0 1
  | 2 => B 0 2
  | 3 => B 0 3
  | 4 => B 1 1
  | 5 => B 1 2
  | 6 => B 1 3
  | 7 => B 2 2
  | 8 => B 2 3
  | _ => B 3 3

theorem tensorEncode_symmetric (x : Fin 10 → ℝ) (i j : Fin 4) :
    tensorEncode x i j = tensorEncode x j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem tensor_encode_decode (B : Tensor2) (hB : ∀ i j, B i j = B j i) :
    tensorEncode (tensorDecode B) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (hB _ _).symm

theorem tensor_decode_encode (x : Fin 10 → ℝ) :
    tensorDecode (tensorEncode x) = x := by
  funext i; fin_cases i <;> rfl

def tensorEncodeLinear : (Fin 10 → ℝ) →ₗ[ℝ] Tensor2 where
  toFun := tensorEncode
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_smul' r x := by ext i j; fin_cases i <;> fin_cases j <;> rfl

def tensorDecodeLinear : Tensor2 →ₗ[ℝ] (Fin 10 → ℝ) where
  toFun := tensorDecode
  map_add' B C := by funext i; fin_cases i <;> rfl
  map_smul' r B := by funext i; fin_cases i <;> rfl

#print axioms tensorEncode_symmetric
#print axioms tensor_encode_decode
#print axioms tensor_decode_encode

end AASCSemanticExhaustion
