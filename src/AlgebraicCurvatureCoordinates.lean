import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Independent algebraic curvature tensors, not a contraction-expression class.
The 20-coordinate representation is proved complete from the four original
tensor laws, including first Bianchi. No completeness field is received. -/
namespace AASCSemanticExhaustion

abbrev Tensor4 := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

def CurvatureLaws (R : Tensor4) : Prop :=
  (∀ a b c d, R a b c d = -R b a c d) ∧
  (∀ a b c d, R a b c d = -R a b d c) ∧
  (∀ a b c d, R a b c d = R c d a b) ∧
  (∀ a b c d, R a b c d + R a c d b + R a d b c = 0)

def curvatureSpace : Submodule ℝ Tensor4 where
  carrier := {R | CurvatureLaws R}
  zero_mem' := by simp [CurvatureLaws]
  add_mem' := by
    intro R S hR hS
    obtain ⟨rf, rl, rp, rb⟩ := hR
    obtain ⟨sf, sl, sp, sb⟩ := hS
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b c d; change R a b c d + S a b c d = -(R b a c d + S b a c d)
      rw [rf a b c d, sf a b c d]; ring
    · intro a b c d; change R a b c d + S a b c d = -(R a b d c + S a b d c)
      rw [rl a b c d, sl a b c d]; ring
    · intro a b c d; change R a b c d + S a b c d = R c d a b + S c d a b
      rw [rp a b c d, sp a b c d]
    · intro a b c d
      change (R a b c d + S a b c d) + (R a c d b + S a c d b) + (R a d b c + S a d b c) = 0
      linarith [rb a b c d, sb a b c d]
  smul_mem' := by
    intro r R hR
    obtain ⟨rf, rl, rp, rb⟩ := hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b c d; change r * R a b c d = -(r * R b a c d)
      rw [rf a b c d]; ring
    · intro a b c d; change r * R a b c d = -(r * R a b d c)
      rw [rl a b c d]; ring
    · intro a b c d; change r * R a b c d = r * R c d a b
      rw [rp a b c d]
    · intro a b c d
      change r * R a b c d + r * R a c d b + r * R a d b c = 0
      calc
        _ = r * (R a b c d + R a c d b + R a d b c) := by ring
        _ = 0 := by rw [rb a b c d, mul_zero]

def curvatureEncode (x : Fin 20 → ℝ) (a b c d : Fin 4) : ℝ :=
  match a.val, b.val, c.val, d.val with
  | 0, 1, 0, 1 => x 0
  | 0, 1, 0, 2 => x 1
  | 0, 1, 0, 3 => x 2
  | 0, 1, 1, 0 => (-x 0)
  | 0, 1, 1, 2 => x 3
  | 0, 1, 1, 3 => x 4
  | 0, 1, 2, 0 => (-x 1)
  | 0, 1, 2, 1 => (-x 3)
  | 0, 1, 2, 3 => x 5
  | 0, 1, 3, 0 => (-x 2)
  | 0, 1, 3, 1 => (-x 4)
  | 0, 1, 3, 2 => (-x 5)
  | 0, 2, 0, 1 => x 1
  | 0, 2, 0, 2 => x 6
  | 0, 2, 0, 3 => x 7
  | 0, 2, 1, 0 => (-x 1)
  | 0, 2, 1, 2 => x 8
  | 0, 2, 1, 3 => x 9
  | 0, 2, 2, 0 => (-x 6)
  | 0, 2, 2, 1 => (-x 8)
  | 0, 2, 2, 3 => x 10
  | 0, 2, 3, 0 => (-x 7)
  | 0, 2, 3, 1 => (-x 9)
  | 0, 2, 3, 2 => (-x 10)
  | 0, 3, 0, 1 => x 2
  | 0, 3, 0, 2 => x 7
  | 0, 3, 0, 3 => x 11
  | 0, 3, 1, 0 => (-x 2)
  | 0, 3, 1, 2 => x 9 + (-x 5)
  | 0, 3, 1, 3 => x 12
  | 0, 3, 2, 0 => (-x 7)
  | 0, 3, 2, 1 => (-x 9) + x 5
  | 0, 3, 2, 3 => x 13
  | 0, 3, 3, 0 => (-x 11)
  | 0, 3, 3, 1 => (-x 12)
  | 0, 3, 3, 2 => (-x 13)
  | 1, 0, 0, 1 => (-x 0)
  | 1, 0, 0, 2 => (-x 1)
  | 1, 0, 0, 3 => (-x 2)
  | 1, 0, 1, 0 => x 0
  | 1, 0, 1, 2 => (-x 3)
  | 1, 0, 1, 3 => (-x 4)
  | 1, 0, 2, 0 => x 1
  | 1, 0, 2, 1 => x 3
  | 1, 0, 2, 3 => (-x 5)
  | 1, 0, 3, 0 => x 2
  | 1, 0, 3, 1 => x 4
  | 1, 0, 3, 2 => x 5
  | 1, 2, 0, 1 => x 3
  | 1, 2, 0, 2 => x 8
  | 1, 2, 0, 3 => x 9 + (-x 5)
  | 1, 2, 1, 0 => (-x 3)
  | 1, 2, 1, 2 => x 14
  | 1, 2, 1, 3 => x 15
  | 1, 2, 2, 0 => (-x 8)
  | 1, 2, 2, 1 => (-x 14)
  | 1, 2, 2, 3 => x 16
  | 1, 2, 3, 0 => (-x 9) + x 5
  | 1, 2, 3, 1 => (-x 15)
  | 1, 2, 3, 2 => (-x 16)
  | 1, 3, 0, 1 => x 4
  | 1, 3, 0, 2 => x 9
  | 1, 3, 0, 3 => x 12
  | 1, 3, 1, 0 => (-x 4)
  | 1, 3, 1, 2 => x 15
  | 1, 3, 1, 3 => x 17
  | 1, 3, 2, 0 => (-x 9)
  | 1, 3, 2, 1 => (-x 15)
  | 1, 3, 2, 3 => x 18
  | 1, 3, 3, 0 => (-x 12)
  | 1, 3, 3, 1 => (-x 17)
  | 1, 3, 3, 2 => (-x 18)
  | 2, 0, 0, 1 => (-x 1)
  | 2, 0, 0, 2 => (-x 6)
  | 2, 0, 0, 3 => (-x 7)
  | 2, 0, 1, 0 => x 1
  | 2, 0, 1, 2 => (-x 8)
  | 2, 0, 1, 3 => (-x 9)
  | 2, 0, 2, 0 => x 6
  | 2, 0, 2, 1 => x 8
  | 2, 0, 2, 3 => (-x 10)
  | 2, 0, 3, 0 => x 7
  | 2, 0, 3, 1 => x 9
  | 2, 0, 3, 2 => x 10
  | 2, 1, 0, 1 => (-x 3)
  | 2, 1, 0, 2 => (-x 8)
  | 2, 1, 0, 3 => (-x 9) + x 5
  | 2, 1, 1, 0 => x 3
  | 2, 1, 1, 2 => (-x 14)
  | 2, 1, 1, 3 => (-x 15)
  | 2, 1, 2, 0 => x 8
  | 2, 1, 2, 1 => x 14
  | 2, 1, 2, 3 => (-x 16)
  | 2, 1, 3, 0 => x 9 + (-x 5)
  | 2, 1, 3, 1 => x 15
  | 2, 1, 3, 2 => x 16
  | 2, 3, 0, 1 => x 5
  | 2, 3, 0, 2 => x 10
  | 2, 3, 0, 3 => x 13
  | 2, 3, 1, 0 => (-x 5)
  | 2, 3, 1, 2 => x 16
  | 2, 3, 1, 3 => x 18
  | 2, 3, 2, 0 => (-x 10)
  | 2, 3, 2, 1 => (-x 16)
  | 2, 3, 2, 3 => x 19
  | 2, 3, 3, 0 => (-x 13)
  | 2, 3, 3, 1 => (-x 18)
  | 2, 3, 3, 2 => (-x 19)
  | 3, 0, 0, 1 => (-x 2)
  | 3, 0, 0, 2 => (-x 7)
  | 3, 0, 0, 3 => (-x 11)
  | 3, 0, 1, 0 => x 2
  | 3, 0, 1, 2 => (-x 9) + x 5
  | 3, 0, 1, 3 => (-x 12)
  | 3, 0, 2, 0 => x 7
  | 3, 0, 2, 1 => x 9 + (-x 5)
  | 3, 0, 2, 3 => (-x 13)
  | 3, 0, 3, 0 => x 11
  | 3, 0, 3, 1 => x 12
  | 3, 0, 3, 2 => x 13
  | 3, 1, 0, 1 => (-x 4)
  | 3, 1, 0, 2 => (-x 9)
  | 3, 1, 0, 3 => (-x 12)
  | 3, 1, 1, 0 => x 4
  | 3, 1, 1, 2 => (-x 15)
  | 3, 1, 1, 3 => (-x 17)
  | 3, 1, 2, 0 => x 9
  | 3, 1, 2, 1 => x 15
  | 3, 1, 2, 3 => (-x 18)
  | 3, 1, 3, 0 => x 12
  | 3, 1, 3, 1 => x 17
  | 3, 1, 3, 2 => x 18
  | 3, 2, 0, 1 => (-x 5)
  | 3, 2, 0, 2 => (-x 10)
  | 3, 2, 0, 3 => (-x 13)
  | 3, 2, 1, 0 => x 5
  | 3, 2, 1, 2 => (-x 16)
  | 3, 2, 1, 3 => (-x 18)
  | 3, 2, 2, 0 => x 10
  | 3, 2, 2, 1 => x 16
  | 3, 2, 2, 3 => (-x 19)
  | 3, 2, 3, 0 => x 13
  | 3, 2, 3, 1 => x 18
  | 3, 2, 3, 2 => x 19
  | _, _, _, _ => 0

set_option maxHeartbeats 0 in
theorem curvatureEncode_mem (x : Fin 20 → ℝ) : CurvatureLaws (curvatureEncode x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [curvatureEncode] <;> ring

def curvatureDecode (R : curvatureSpace) (i : Fin 20) : ℝ :=
  match i.val with
  | 0 => (R : Tensor4) 0 1 0 1
  | 1 => (R : Tensor4) 0 1 0 2
  | 2 => (R : Tensor4) 0 1 0 3
  | 3 => (R : Tensor4) 0 1 1 2
  | 4 => (R : Tensor4) 0 1 1 3
  | 5 => (R : Tensor4) 0 1 2 3
  | 6 => (R : Tensor4) 0 2 0 2
  | 7 => (R : Tensor4) 0 2 0 3
  | 8 => (R : Tensor4) 0 2 1 2
  | 9 => (R : Tensor4) 0 2 1 3
  | 10 => (R : Tensor4) 0 2 2 3
  | 11 => (R : Tensor4) 0 3 0 3
  | 12 => (R : Tensor4) 0 3 1 3
  | 13 => (R : Tensor4) 0 3 2 3
  | 14 => (R : Tensor4) 1 2 1 2
  | 15 => (R : Tensor4) 1 2 1 3
  | 16 => (R : Tensor4) 1 2 2 3
  | 17 => (R : Tensor4) 1 3 1 3
  | 18 => (R : Tensor4) 1 3 2 3
  | 19 => (R : Tensor4) 2 3 2 3
  | _ => 0

set_option maxHeartbeats 0 in
theorem curvature_encode_decode (R : curvatureSpace) :
    curvatureEncode (curvatureDecode R) = (R : Tensor4) := by
  have hspecial : (R : Tensor4) 0 3 1 2 = (R : Tensor4) 0 2 1 3 - (R : Tensor4) 0 1 2 3 := by
    have hb := R.property.2.2.2 0 1 2 3
    have hs := R.property.2.1 0 2 3 1
    linarith
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · change (0 : ℝ) = (R : Tensor4) 0 0 0 0
    have h := R.property.1 0 0 0 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 0 1
    have h := R.property.1 0 0 0 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 0 2
    have h := R.property.1 0 0 0 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 0 3
    have h := R.property.1 0 0 0 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 1 0
    have h := R.property.1 0 0 1 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 1 1
    have h := R.property.1 0 0 1 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 1 2
    have h := R.property.1 0 0 1 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 1 3
    have h := R.property.1 0 0 1 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 2 0
    have h := R.property.1 0 0 2 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 2 1
    have h := R.property.1 0 0 2 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 2 2
    have h := R.property.1 0 0 2 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 2 3
    have h := R.property.1 0 0 2 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 3 0
    have h := R.property.1 0 0 3 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 3 1
    have h := R.property.1 0 0 3 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 3 2
    have h := R.property.1 0 0 3 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 0 3 3
    have h := R.property.1 0 0 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 1 0 0
    have h := R.property.2.1 0 1 0 0
    linarith only [h]
  · change (R : Tensor4) 0 1 0 1 = (R : Tensor4) 0 1 0 1
    rfl
  · change (R : Tensor4) 0 1 0 2 = (R : Tensor4) 0 1 0 2
    rfl
  · change (R : Tensor4) 0 1 0 3 = (R : Tensor4) 0 1 0 3
    rfl
  · change (-(R : Tensor4) 0 1 0 1) = (R : Tensor4) 0 1 1 0
    have hl := R.property.2.1 0 1 1 0
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 0 1 1 1
    have h := R.property.2.1 0 1 1 1
    linarith only [h]
  · change (R : Tensor4) 0 1 1 2 = (R : Tensor4) 0 1 1 2
    rfl
  · change (R : Tensor4) 0 1 1 3 = (R : Tensor4) 0 1 1 3
    rfl
  · change (-(R : Tensor4) 0 1 0 2) = (R : Tensor4) 0 1 2 0
    have hl := R.property.2.1 0 1 2 0
    linarith only [hl]
  · change (-(R : Tensor4) 0 1 1 2) = (R : Tensor4) 0 1 2 1
    have hl := R.property.2.1 0 1 2 1
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 0 1 2 2
    have h := R.property.2.1 0 1 2 2
    linarith only [h]
  · change (R : Tensor4) 0 1 2 3 = (R : Tensor4) 0 1 2 3
    rfl
  · change (-(R : Tensor4) 0 1 0 3) = (R : Tensor4) 0 1 3 0
    have hl := R.property.2.1 0 1 3 0
    linarith only [hl]
  · change (-(R : Tensor4) 0 1 1 3) = (R : Tensor4) 0 1 3 1
    have hl := R.property.2.1 0 1 3 1
    linarith only [hl]
  · change (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 0 1 3 2
    have hl := R.property.2.1 0 1 3 2
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 0 1 3 3
    have h := R.property.2.1 0 1 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 2 0 0
    have h := R.property.2.1 0 2 0 0
    linarith only [h]
  · change (R : Tensor4) 0 1 0 2 = (R : Tensor4) 0 2 0 1
    have hp := R.property.2.2.1 0 2 0 1
    linarith only [hp]
  · change (R : Tensor4) 0 2 0 2 = (R : Tensor4) 0 2 0 2
    rfl
  · change (R : Tensor4) 0 2 0 3 = (R : Tensor4) 0 2 0 3
    rfl
  · change (-(R : Tensor4) 0 1 0 2) = (R : Tensor4) 0 2 1 0
    have hl := R.property.2.1 0 2 1 0
    have hp := R.property.2.2.1 0 2 0 1
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 0 2 1 1
    have h := R.property.2.1 0 2 1 1
    linarith only [h]
  · change (R : Tensor4) 0 2 1 2 = (R : Tensor4) 0 2 1 2
    rfl
  · change (R : Tensor4) 0 2 1 3 = (R : Tensor4) 0 2 1 3
    rfl
  · change (-(R : Tensor4) 0 2 0 2) = (R : Tensor4) 0 2 2 0
    have hl := R.property.2.1 0 2 2 0
    linarith only [hl]
  · change (-(R : Tensor4) 0 2 1 2) = (R : Tensor4) 0 2 2 1
    have hl := R.property.2.1 0 2 2 1
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 0 2 2 2
    have h := R.property.2.1 0 2 2 2
    linarith only [h]
  · change (R : Tensor4) 0 2 2 3 = (R : Tensor4) 0 2 2 3
    rfl
  · change (-(R : Tensor4) 0 2 0 3) = (R : Tensor4) 0 2 3 0
    have hl := R.property.2.1 0 2 3 0
    linarith only [hl]
  · change (-(R : Tensor4) 0 2 1 3) = (R : Tensor4) 0 2 3 1
    have hl := R.property.2.1 0 2 3 1
    linarith only [hl]
  · change (-(R : Tensor4) 0 2 2 3) = (R : Tensor4) 0 2 3 2
    have hl := R.property.2.1 0 2 3 2
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 0 2 3 3
    have h := R.property.2.1 0 2 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 0 3 0 0
    have h := R.property.2.1 0 3 0 0
    linarith only [h]
  · change (R : Tensor4) 0 1 0 3 = (R : Tensor4) 0 3 0 1
    have hp := R.property.2.2.1 0 3 0 1
    linarith only [hp]
  · change (R : Tensor4) 0 2 0 3 = (R : Tensor4) 0 3 0 2
    have hp := R.property.2.2.1 0 3 0 2
    linarith only [hp]
  · change (R : Tensor4) 0 3 0 3 = (R : Tensor4) 0 3 0 3
    rfl
  · change (-(R : Tensor4) 0 1 0 3) = (R : Tensor4) 0 3 1 0
    have hl := R.property.2.1 0 3 1 0
    have hp := R.property.2.2.1 0 3 0 1
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 0 3 1 1
    have h := R.property.2.1 0 3 1 1
    linarith only [h]
  · change (R : Tensor4) 0 2 1 3 + (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 0 3 1 2
    linarith only [hspecial]
  · change (R : Tensor4) 0 3 1 3 = (R : Tensor4) 0 3 1 3
    rfl
  · change (-(R : Tensor4) 0 2 0 3) = (R : Tensor4) 0 3 2 0
    have hl := R.property.2.1 0 3 2 0
    have hp := R.property.2.2.1 0 3 0 2
    linarith only [hl, hp]
  · change (-(R : Tensor4) 0 2 1 3) + (R : Tensor4) 0 1 2 3 = (R : Tensor4) 0 3 2 1
    have hl := R.property.2.1 0 3 2 1
    linarith only [hl, hspecial]
  · change (0 : ℝ) = (R : Tensor4) 0 3 2 2
    have h := R.property.2.1 0 3 2 2
    linarith only [h]
  · change (R : Tensor4) 0 3 2 3 = (R : Tensor4) 0 3 2 3
    rfl
  · change (-(R : Tensor4) 0 3 0 3) = (R : Tensor4) 0 3 3 0
    have hl := R.property.2.1 0 3 3 0
    linarith only [hl]
  · change (-(R : Tensor4) 0 3 1 3) = (R : Tensor4) 0 3 3 1
    have hl := R.property.2.1 0 3 3 1
    linarith only [hl]
  · change (-(R : Tensor4) 0 3 2 3) = (R : Tensor4) 0 3 3 2
    have hl := R.property.2.1 0 3 3 2
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 0 3 3 3
    have h := R.property.2.1 0 3 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 0 0 0
    have h := R.property.2.1 1 0 0 0
    linarith only [h]
  · change (-(R : Tensor4) 0 1 0 1) = (R : Tensor4) 1 0 0 1
    have hf := R.property.1 1 0 0 1
    linarith only [hf]
  · change (-(R : Tensor4) 0 1 0 2) = (R : Tensor4) 1 0 0 2
    have hf := R.property.1 1 0 0 2
    linarith only [hf]
  · change (-(R : Tensor4) 0 1 0 3) = (R : Tensor4) 1 0 0 3
    have hf := R.property.1 1 0 0 3
    linarith only [hf]
  · change (R : Tensor4) 0 1 0 1 = (R : Tensor4) 1 0 1 0
    have hf := R.property.1 1 0 1 0
    have hl := R.property.2.1 0 1 1 0
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 1 0 1 1
    have h := R.property.2.1 1 0 1 1
    linarith only [h]
  · change (-(R : Tensor4) 0 1 1 2) = (R : Tensor4) 1 0 1 2
    have hf := R.property.1 1 0 1 2
    linarith only [hf]
  · change (-(R : Tensor4) 0 1 1 3) = (R : Tensor4) 1 0 1 3
    have hf := R.property.1 1 0 1 3
    linarith only [hf]
  · change (R : Tensor4) 0 1 0 2 = (R : Tensor4) 1 0 2 0
    have hf := R.property.1 1 0 2 0
    have hl := R.property.2.1 0 1 2 0
    linarith only [hf, hl]
  · change (R : Tensor4) 0 1 1 2 = (R : Tensor4) 1 0 2 1
    have hf := R.property.1 1 0 2 1
    have hl := R.property.2.1 0 1 2 1
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 1 0 2 2
    have h := R.property.2.1 1 0 2 2
    linarith only [h]
  · change (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 1 0 2 3
    have hf := R.property.1 1 0 2 3
    linarith only [hf]
  · change (R : Tensor4) 0 1 0 3 = (R : Tensor4) 1 0 3 0
    have hf := R.property.1 1 0 3 0
    have hl := R.property.2.1 0 1 3 0
    linarith only [hf, hl]
  · change (R : Tensor4) 0 1 1 3 = (R : Tensor4) 1 0 3 1
    have hf := R.property.1 1 0 3 1
    have hl := R.property.2.1 0 1 3 1
    linarith only [hf, hl]
  · change (R : Tensor4) 0 1 2 3 = (R : Tensor4) 1 0 3 2
    have hf := R.property.1 1 0 3 2
    have hl := R.property.2.1 0 1 3 2
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 1 0 3 3
    have h := R.property.2.1 1 0 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 0 0
    have h := R.property.1 1 1 0 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 0 1
    have h := R.property.1 1 1 0 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 0 2
    have h := R.property.1 1 1 0 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 0 3
    have h := R.property.1 1 1 0 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 1 0
    have h := R.property.1 1 1 1 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 1 1
    have h := R.property.1 1 1 1 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 1 2
    have h := R.property.1 1 1 1 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 1 3
    have h := R.property.1 1 1 1 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 2 0
    have h := R.property.1 1 1 2 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 2 1
    have h := R.property.1 1 1 2 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 2 2
    have h := R.property.1 1 1 2 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 2 3
    have h := R.property.1 1 1 2 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 3 0
    have h := R.property.1 1 1 3 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 3 1
    have h := R.property.1 1 1 3 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 3 2
    have h := R.property.1 1 1 3 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 1 3 3
    have h := R.property.1 1 1 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 2 0 0
    have h := R.property.2.1 1 2 0 0
    linarith only [h]
  · change (R : Tensor4) 0 1 1 2 = (R : Tensor4) 1 2 0 1
    have hp := R.property.2.2.1 1 2 0 1
    linarith only [hp]
  · change (R : Tensor4) 0 2 1 2 = (R : Tensor4) 1 2 0 2
    have hp := R.property.2.2.1 1 2 0 2
    linarith only [hp]
  · change (R : Tensor4) 0 2 1 3 + (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 1 2 0 3
    have hp := R.property.2.2.1 1 2 0 3
    linarith only [hp, hspecial]
  · change (-(R : Tensor4) 0 1 1 2) = (R : Tensor4) 1 2 1 0
    have hl := R.property.2.1 1 2 1 0
    have hp := R.property.2.2.1 1 2 0 1
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 1 2 1 1
    have h := R.property.2.1 1 2 1 1
    linarith only [h]
  · change (R : Tensor4) 1 2 1 2 = (R : Tensor4) 1 2 1 2
    rfl
  · change (R : Tensor4) 1 2 1 3 = (R : Tensor4) 1 2 1 3
    rfl
  · change (-(R : Tensor4) 0 2 1 2) = (R : Tensor4) 1 2 2 0
    have hl := R.property.2.1 1 2 2 0
    have hp := R.property.2.2.1 1 2 0 2
    linarith only [hl, hp]
  · change (-(R : Tensor4) 1 2 1 2) = (R : Tensor4) 1 2 2 1
    have hl := R.property.2.1 1 2 2 1
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 1 2 2 2
    have h := R.property.2.1 1 2 2 2
    linarith only [h]
  · change (R : Tensor4) 1 2 2 3 = (R : Tensor4) 1 2 2 3
    rfl
  · change (-(R : Tensor4) 0 2 1 3) + (R : Tensor4) 0 1 2 3 = (R : Tensor4) 1 2 3 0
    have hl := R.property.2.1 1 2 3 0
    have hp := R.property.2.2.1 1 2 0 3
    linarith only [hl, hp, hspecial]
  · change (-(R : Tensor4) 1 2 1 3) = (R : Tensor4) 1 2 3 1
    have hl := R.property.2.1 1 2 3 1
    linarith only [hl]
  · change (-(R : Tensor4) 1 2 2 3) = (R : Tensor4) 1 2 3 2
    have hl := R.property.2.1 1 2 3 2
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 1 2 3 3
    have h := R.property.2.1 1 2 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 1 3 0 0
    have h := R.property.2.1 1 3 0 0
    linarith only [h]
  · change (R : Tensor4) 0 1 1 3 = (R : Tensor4) 1 3 0 1
    have hp := R.property.2.2.1 1 3 0 1
    linarith only [hp]
  · change (R : Tensor4) 0 2 1 3 = (R : Tensor4) 1 3 0 2
    have hp := R.property.2.2.1 1 3 0 2
    linarith only [hp]
  · change (R : Tensor4) 0 3 1 3 = (R : Tensor4) 1 3 0 3
    have hp := R.property.2.2.1 1 3 0 3
    linarith only [hp]
  · change (-(R : Tensor4) 0 1 1 3) = (R : Tensor4) 1 3 1 0
    have hl := R.property.2.1 1 3 1 0
    have hp := R.property.2.2.1 1 3 0 1
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 1 3 1 1
    have h := R.property.2.1 1 3 1 1
    linarith only [h]
  · change (R : Tensor4) 1 2 1 3 = (R : Tensor4) 1 3 1 2
    have hp := R.property.2.2.1 1 3 1 2
    linarith only [hp]
  · change (R : Tensor4) 1 3 1 3 = (R : Tensor4) 1 3 1 3
    rfl
  · change (-(R : Tensor4) 0 2 1 3) = (R : Tensor4) 1 3 2 0
    have hl := R.property.2.1 1 3 2 0
    have hp := R.property.2.2.1 1 3 0 2
    linarith only [hl, hp]
  · change (-(R : Tensor4) 1 2 1 3) = (R : Tensor4) 1 3 2 1
    have hl := R.property.2.1 1 3 2 1
    have hp := R.property.2.2.1 1 3 1 2
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 1 3 2 2
    have h := R.property.2.1 1 3 2 2
    linarith only [h]
  · change (R : Tensor4) 1 3 2 3 = (R : Tensor4) 1 3 2 3
    rfl
  · change (-(R : Tensor4) 0 3 1 3) = (R : Tensor4) 1 3 3 0
    have hl := R.property.2.1 1 3 3 0
    have hp := R.property.2.2.1 1 3 0 3
    linarith only [hl, hp]
  · change (-(R : Tensor4) 1 3 1 3) = (R : Tensor4) 1 3 3 1
    have hl := R.property.2.1 1 3 3 1
    linarith only [hl]
  · change (-(R : Tensor4) 1 3 2 3) = (R : Tensor4) 1 3 3 2
    have hl := R.property.2.1 1 3 3 2
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 1 3 3 3
    have h := R.property.2.1 1 3 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 0 0 0
    have h := R.property.2.1 2 0 0 0
    linarith only [h]
  · change (-(R : Tensor4) 0 1 0 2) = (R : Tensor4) 2 0 0 1
    have hf := R.property.1 2 0 0 1
    have hp := R.property.2.2.1 0 2 0 1
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 2 0 2) = (R : Tensor4) 2 0 0 2
    have hf := R.property.1 2 0 0 2
    linarith only [hf]
  · change (-(R : Tensor4) 0 2 0 3) = (R : Tensor4) 2 0 0 3
    have hf := R.property.1 2 0 0 3
    linarith only [hf]
  · change (R : Tensor4) 0 1 0 2 = (R : Tensor4) 2 0 1 0
    have hf := R.property.1 2 0 1 0
    have hl := R.property.2.1 0 2 1 0
    have hp := R.property.2.2.1 0 2 0 1
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 2 0 1 1
    have h := R.property.2.1 2 0 1 1
    linarith only [h]
  · change (-(R : Tensor4) 0 2 1 2) = (R : Tensor4) 2 0 1 2
    have hf := R.property.1 2 0 1 2
    linarith only [hf]
  · change (-(R : Tensor4) 0 2 1 3) = (R : Tensor4) 2 0 1 3
    have hf := R.property.1 2 0 1 3
    linarith only [hf]
  · change (R : Tensor4) 0 2 0 2 = (R : Tensor4) 2 0 2 0
    have hf := R.property.1 2 0 2 0
    have hl := R.property.2.1 0 2 2 0
    linarith only [hf, hl]
  · change (R : Tensor4) 0 2 1 2 = (R : Tensor4) 2 0 2 1
    have hf := R.property.1 2 0 2 1
    have hl := R.property.2.1 0 2 2 1
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 2 0 2 2
    have h := R.property.2.1 2 0 2 2
    linarith only [h]
  · change (-(R : Tensor4) 0 2 2 3) = (R : Tensor4) 2 0 2 3
    have hf := R.property.1 2 0 2 3
    linarith only [hf]
  · change (R : Tensor4) 0 2 0 3 = (R : Tensor4) 2 0 3 0
    have hf := R.property.1 2 0 3 0
    have hl := R.property.2.1 0 2 3 0
    linarith only [hf, hl]
  · change (R : Tensor4) 0 2 1 3 = (R : Tensor4) 2 0 3 1
    have hf := R.property.1 2 0 3 1
    have hl := R.property.2.1 0 2 3 1
    linarith only [hf, hl]
  · change (R : Tensor4) 0 2 2 3 = (R : Tensor4) 2 0 3 2
    have hf := R.property.1 2 0 3 2
    have hl := R.property.2.1 0 2 3 2
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 2 0 3 3
    have h := R.property.2.1 2 0 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 1 0 0
    have h := R.property.2.1 2 1 0 0
    linarith only [h]
  · change (-(R : Tensor4) 0 1 1 2) = (R : Tensor4) 2 1 0 1
    have hf := R.property.1 2 1 0 1
    have hp := R.property.2.2.1 1 2 0 1
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 2 1 2) = (R : Tensor4) 2 1 0 2
    have hf := R.property.1 2 1 0 2
    have hp := R.property.2.2.1 1 2 0 2
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 2 1 3) + (R : Tensor4) 0 1 2 3 = (R : Tensor4) 2 1 0 3
    have hf := R.property.1 2 1 0 3
    have hp := R.property.2.2.1 1 2 0 3
    linarith only [hf, hp, hspecial]
  · change (R : Tensor4) 0 1 1 2 = (R : Tensor4) 2 1 1 0
    have hf := R.property.1 2 1 1 0
    have hl := R.property.2.1 1 2 1 0
    have hp := R.property.2.2.1 1 2 0 1
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 2 1 1 1
    have h := R.property.2.1 2 1 1 1
    linarith only [h]
  · change (-(R : Tensor4) 1 2 1 2) = (R : Tensor4) 2 1 1 2
    have hf := R.property.1 2 1 1 2
    linarith only [hf]
  · change (-(R : Tensor4) 1 2 1 3) = (R : Tensor4) 2 1 1 3
    have hf := R.property.1 2 1 1 3
    linarith only [hf]
  · change (R : Tensor4) 0 2 1 2 = (R : Tensor4) 2 1 2 0
    have hf := R.property.1 2 1 2 0
    have hl := R.property.2.1 1 2 2 0
    have hp := R.property.2.2.1 1 2 0 2
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 1 2 1 2 = (R : Tensor4) 2 1 2 1
    have hf := R.property.1 2 1 2 1
    have hl := R.property.2.1 1 2 2 1
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 2 1 2 2
    have h := R.property.2.1 2 1 2 2
    linarith only [h]
  · change (-(R : Tensor4) 1 2 2 3) = (R : Tensor4) 2 1 2 3
    have hf := R.property.1 2 1 2 3
    linarith only [hf]
  · change (R : Tensor4) 0 2 1 3 + (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 2 1 3 0
    have hf := R.property.1 2 1 3 0
    have hl := R.property.2.1 1 2 3 0
    have hp := R.property.2.2.1 1 2 0 3
    linarith only [hf, hl, hp, hspecial]
  · change (R : Tensor4) 1 2 1 3 = (R : Tensor4) 2 1 3 1
    have hf := R.property.1 2 1 3 1
    have hl := R.property.2.1 1 2 3 1
    linarith only [hf, hl]
  · change (R : Tensor4) 1 2 2 3 = (R : Tensor4) 2 1 3 2
    have hf := R.property.1 2 1 3 2
    have hl := R.property.2.1 1 2 3 2
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 2 1 3 3
    have h := R.property.2.1 2 1 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 0 0
    have h := R.property.1 2 2 0 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 0 1
    have h := R.property.1 2 2 0 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 0 2
    have h := R.property.1 2 2 0 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 0 3
    have h := R.property.1 2 2 0 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 1 0
    have h := R.property.1 2 2 1 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 1 1
    have h := R.property.1 2 2 1 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 1 2
    have h := R.property.1 2 2 1 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 1 3
    have h := R.property.1 2 2 1 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 2 0
    have h := R.property.1 2 2 2 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 2 1
    have h := R.property.1 2 2 2 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 2 2
    have h := R.property.1 2 2 2 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 2 3
    have h := R.property.1 2 2 2 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 3 0
    have h := R.property.1 2 2 3 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 3 1
    have h := R.property.1 2 2 3 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 3 2
    have h := R.property.1 2 2 3 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 2 3 3
    have h := R.property.1 2 2 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 2 3 0 0
    have h := R.property.2.1 2 3 0 0
    linarith only [h]
  · change (R : Tensor4) 0 1 2 3 = (R : Tensor4) 2 3 0 1
    have hp := R.property.2.2.1 2 3 0 1
    linarith only [hp]
  · change (R : Tensor4) 0 2 2 3 = (R : Tensor4) 2 3 0 2
    have hp := R.property.2.2.1 2 3 0 2
    linarith only [hp]
  · change (R : Tensor4) 0 3 2 3 = (R : Tensor4) 2 3 0 3
    have hp := R.property.2.2.1 2 3 0 3
    linarith only [hp]
  · change (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 2 3 1 0
    have hl := R.property.2.1 2 3 1 0
    have hp := R.property.2.2.1 2 3 0 1
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 2 3 1 1
    have h := R.property.2.1 2 3 1 1
    linarith only [h]
  · change (R : Tensor4) 1 2 2 3 = (R : Tensor4) 2 3 1 2
    have hp := R.property.2.2.1 2 3 1 2
    linarith only [hp]
  · change (R : Tensor4) 1 3 2 3 = (R : Tensor4) 2 3 1 3
    have hp := R.property.2.2.1 2 3 1 3
    linarith only [hp]
  · change (-(R : Tensor4) 0 2 2 3) = (R : Tensor4) 2 3 2 0
    have hl := R.property.2.1 2 3 2 0
    have hp := R.property.2.2.1 2 3 0 2
    linarith only [hl, hp]
  · change (-(R : Tensor4) 1 2 2 3) = (R : Tensor4) 2 3 2 1
    have hl := R.property.2.1 2 3 2 1
    have hp := R.property.2.2.1 2 3 1 2
    linarith only [hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 2 3 2 2
    have h := R.property.2.1 2 3 2 2
    linarith only [h]
  · change (R : Tensor4) 2 3 2 3 = (R : Tensor4) 2 3 2 3
    rfl
  · change (-(R : Tensor4) 0 3 2 3) = (R : Tensor4) 2 3 3 0
    have hl := R.property.2.1 2 3 3 0
    have hp := R.property.2.2.1 2 3 0 3
    linarith only [hl, hp]
  · change (-(R : Tensor4) 1 3 2 3) = (R : Tensor4) 2 3 3 1
    have hl := R.property.2.1 2 3 3 1
    have hp := R.property.2.2.1 2 3 1 3
    linarith only [hl, hp]
  · change (-(R : Tensor4) 2 3 2 3) = (R : Tensor4) 2 3 3 2
    have hl := R.property.2.1 2 3 3 2
    linarith only [hl]
  · change (0 : ℝ) = (R : Tensor4) 2 3 3 3
    have h := R.property.2.1 2 3 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 0 0 0
    have h := R.property.2.1 3 0 0 0
    linarith only [h]
  · change (-(R : Tensor4) 0 1 0 3) = (R : Tensor4) 3 0 0 1
    have hf := R.property.1 3 0 0 1
    have hp := R.property.2.2.1 0 3 0 1
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 2 0 3) = (R : Tensor4) 3 0 0 2
    have hf := R.property.1 3 0 0 2
    have hp := R.property.2.2.1 0 3 0 2
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 3 0 3) = (R : Tensor4) 3 0 0 3
    have hf := R.property.1 3 0 0 3
    linarith only [hf]
  · change (R : Tensor4) 0 1 0 3 = (R : Tensor4) 3 0 1 0
    have hf := R.property.1 3 0 1 0
    have hl := R.property.2.1 0 3 1 0
    have hp := R.property.2.2.1 0 3 0 1
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 3 0 1 1
    have h := R.property.2.1 3 0 1 1
    linarith only [h]
  · change (-(R : Tensor4) 0 2 1 3) + (R : Tensor4) 0 1 2 3 = (R : Tensor4) 3 0 1 2
    have hf := R.property.1 3 0 1 2
    linarith only [hf, hspecial]
  · change (-(R : Tensor4) 0 3 1 3) = (R : Tensor4) 3 0 1 3
    have hf := R.property.1 3 0 1 3
    linarith only [hf]
  · change (R : Tensor4) 0 2 0 3 = (R : Tensor4) 3 0 2 0
    have hf := R.property.1 3 0 2 0
    have hl := R.property.2.1 0 3 2 0
    have hp := R.property.2.2.1 0 3 0 2
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 0 2 1 3 + (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 3 0 2 1
    have hf := R.property.1 3 0 2 1
    have hl := R.property.2.1 0 3 2 1
    linarith only [hf, hl, hspecial]
  · change (0 : ℝ) = (R : Tensor4) 3 0 2 2
    have h := R.property.2.1 3 0 2 2
    linarith only [h]
  · change (-(R : Tensor4) 0 3 2 3) = (R : Tensor4) 3 0 2 3
    have hf := R.property.1 3 0 2 3
    linarith only [hf]
  · change (R : Tensor4) 0 3 0 3 = (R : Tensor4) 3 0 3 0
    have hf := R.property.1 3 0 3 0
    have hl := R.property.2.1 0 3 3 0
    linarith only [hf, hl]
  · change (R : Tensor4) 0 3 1 3 = (R : Tensor4) 3 0 3 1
    have hf := R.property.1 3 0 3 1
    have hl := R.property.2.1 0 3 3 1
    linarith only [hf, hl]
  · change (R : Tensor4) 0 3 2 3 = (R : Tensor4) 3 0 3 2
    have hf := R.property.1 3 0 3 2
    have hl := R.property.2.1 0 3 3 2
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 3 0 3 3
    have h := R.property.2.1 3 0 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 1 0 0
    have h := R.property.2.1 3 1 0 0
    linarith only [h]
  · change (-(R : Tensor4) 0 1 1 3) = (R : Tensor4) 3 1 0 1
    have hf := R.property.1 3 1 0 1
    have hp := R.property.2.2.1 1 3 0 1
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 2 1 3) = (R : Tensor4) 3 1 0 2
    have hf := R.property.1 3 1 0 2
    have hp := R.property.2.2.1 1 3 0 2
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 3 1 3) = (R : Tensor4) 3 1 0 3
    have hf := R.property.1 3 1 0 3
    have hp := R.property.2.2.1 1 3 0 3
    linarith only [hf, hp]
  · change (R : Tensor4) 0 1 1 3 = (R : Tensor4) 3 1 1 0
    have hf := R.property.1 3 1 1 0
    have hl := R.property.2.1 1 3 1 0
    have hp := R.property.2.2.1 1 3 0 1
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 3 1 1 1
    have h := R.property.2.1 3 1 1 1
    linarith only [h]
  · change (-(R : Tensor4) 1 2 1 3) = (R : Tensor4) 3 1 1 2
    have hf := R.property.1 3 1 1 2
    have hp := R.property.2.2.1 1 3 1 2
    linarith only [hf, hp]
  · change (-(R : Tensor4) 1 3 1 3) = (R : Tensor4) 3 1 1 3
    have hf := R.property.1 3 1 1 3
    linarith only [hf]
  · change (R : Tensor4) 0 2 1 3 = (R : Tensor4) 3 1 2 0
    have hf := R.property.1 3 1 2 0
    have hl := R.property.2.1 1 3 2 0
    have hp := R.property.2.2.1 1 3 0 2
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 1 2 1 3 = (R : Tensor4) 3 1 2 1
    have hf := R.property.1 3 1 2 1
    have hl := R.property.2.1 1 3 2 1
    have hp := R.property.2.2.1 1 3 1 2
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 3 1 2 2
    have h := R.property.2.1 3 1 2 2
    linarith only [h]
  · change (-(R : Tensor4) 1 3 2 3) = (R : Tensor4) 3 1 2 3
    have hf := R.property.1 3 1 2 3
    linarith only [hf]
  · change (R : Tensor4) 0 3 1 3 = (R : Tensor4) 3 1 3 0
    have hf := R.property.1 3 1 3 0
    have hl := R.property.2.1 1 3 3 0
    have hp := R.property.2.2.1 1 3 0 3
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 1 3 1 3 = (R : Tensor4) 3 1 3 1
    have hf := R.property.1 3 1 3 1
    have hl := R.property.2.1 1 3 3 1
    linarith only [hf, hl]
  · change (R : Tensor4) 1 3 2 3 = (R : Tensor4) 3 1 3 2
    have hf := R.property.1 3 1 3 2
    have hl := R.property.2.1 1 3 3 2
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 3 1 3 3
    have h := R.property.2.1 3 1 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 2 0 0
    have h := R.property.2.1 3 2 0 0
    linarith only [h]
  · change (-(R : Tensor4) 0 1 2 3) = (R : Tensor4) 3 2 0 1
    have hf := R.property.1 3 2 0 1
    have hp := R.property.2.2.1 2 3 0 1
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 2 2 3) = (R : Tensor4) 3 2 0 2
    have hf := R.property.1 3 2 0 2
    have hp := R.property.2.2.1 2 3 0 2
    linarith only [hf, hp]
  · change (-(R : Tensor4) 0 3 2 3) = (R : Tensor4) 3 2 0 3
    have hf := R.property.1 3 2 0 3
    have hp := R.property.2.2.1 2 3 0 3
    linarith only [hf, hp]
  · change (R : Tensor4) 0 1 2 3 = (R : Tensor4) 3 2 1 0
    have hf := R.property.1 3 2 1 0
    have hl := R.property.2.1 2 3 1 0
    have hp := R.property.2.2.1 2 3 0 1
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 3 2 1 1
    have h := R.property.2.1 3 2 1 1
    linarith only [h]
  · change (-(R : Tensor4) 1 2 2 3) = (R : Tensor4) 3 2 1 2
    have hf := R.property.1 3 2 1 2
    have hp := R.property.2.2.1 2 3 1 2
    linarith only [hf, hp]
  · change (-(R : Tensor4) 1 3 2 3) = (R : Tensor4) 3 2 1 3
    have hf := R.property.1 3 2 1 3
    have hp := R.property.2.2.1 2 3 1 3
    linarith only [hf, hp]
  · change (R : Tensor4) 0 2 2 3 = (R : Tensor4) 3 2 2 0
    have hf := R.property.1 3 2 2 0
    have hl := R.property.2.1 2 3 2 0
    have hp := R.property.2.2.1 2 3 0 2
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 1 2 2 3 = (R : Tensor4) 3 2 2 1
    have hf := R.property.1 3 2 2 1
    have hl := R.property.2.1 2 3 2 1
    have hp := R.property.2.2.1 2 3 1 2
    linarith only [hf, hl, hp]
  · change (0 : ℝ) = (R : Tensor4) 3 2 2 2
    have h := R.property.2.1 3 2 2 2
    linarith only [h]
  · change (-(R : Tensor4) 2 3 2 3) = (R : Tensor4) 3 2 2 3
    have hf := R.property.1 3 2 2 3
    linarith only [hf]
  · change (R : Tensor4) 0 3 2 3 = (R : Tensor4) 3 2 3 0
    have hf := R.property.1 3 2 3 0
    have hl := R.property.2.1 2 3 3 0
    have hp := R.property.2.2.1 2 3 0 3
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 1 3 2 3 = (R : Tensor4) 3 2 3 1
    have hf := R.property.1 3 2 3 1
    have hl := R.property.2.1 2 3 3 1
    have hp := R.property.2.2.1 2 3 1 3
    linarith only [hf, hl, hp]
  · change (R : Tensor4) 2 3 2 3 = (R : Tensor4) 3 2 3 2
    have hf := R.property.1 3 2 3 2
    have hl := R.property.2.1 2 3 3 2
    linarith only [hf, hl]
  · change (0 : ℝ) = (R : Tensor4) 3 2 3 3
    have h := R.property.2.1 3 2 3 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 0 0
    have h := R.property.1 3 3 0 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 0 1
    have h := R.property.1 3 3 0 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 0 2
    have h := R.property.1 3 3 0 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 0 3
    have h := R.property.1 3 3 0 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 1 0
    have h := R.property.1 3 3 1 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 1 1
    have h := R.property.1 3 3 1 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 1 2
    have h := R.property.1 3 3 1 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 1 3
    have h := R.property.1 3 3 1 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 2 0
    have h := R.property.1 3 3 2 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 2 1
    have h := R.property.1 3 3 2 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 2 2
    have h := R.property.1 3 3 2 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 2 3
    have h := R.property.1 3 3 2 3
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 3 0
    have h := R.property.1 3 3 3 0
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 3 1
    have h := R.property.1 3 3 3 1
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 3 2
    have h := R.property.1 3 3 3 2
    linarith only [h]
  · change (0 : ℝ) = (R : Tensor4) 3 3 3 3
    have h := R.property.1 3 3 3 3
    linarith only [h]

theorem curvature_decode_encode (x : Fin 20 → ℝ) :
    curvatureDecode ⟨curvatureEncode x, curvatureEncode_mem x⟩ = x := by
  funext i; fin_cases i <;> rfl

#print axioms curvatureEncode_mem
#print axioms curvature_encode_decode
#print axioms curvature_decode_encode
end AASCSemanticExhaustion
