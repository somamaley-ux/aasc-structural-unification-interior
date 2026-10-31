import OriginalEHPalatiniContractionAlgebra

/-! Reindexing of the actual derivative terms and distribution of the
weighted inverse compatibility terms. No differential identity is assumed. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators

def ehSum3 (F : Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, F a b c

theorem eh_sum3_congr (F G : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ a b c, F a b c = G a b c) : ehSum3 F = ehSum3 G := by
  unfold ehSum3
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  exact h a b c

theorem eh_sum3_swap12 (F : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum3 F = ehSum3 (fun a b c => F b a c) := by
  unfold ehSum3
  exact Finset.sum_comm

theorem eh_sum3_rotate (F : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum3 F = ehSum3 (fun a b c => F c a b) := by
  rw [eh_sum3_swap12 F]
  unfold ehSum3
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem eh_palatini_derivative_contraction_algebra
    (B : Tensor2) (D : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ds : ∀ a b c r, D a b c r = D a c b r) :
    ehSum3 (fun c a b => B a b * D c a b c - B a c * D b a b c) =
      ehSum3 (fun a b c => B a b * (D c b a c - D c c a b)) := by
  have h1 : ehSum3 (fun c a b => B a b * D c a b c) =
      ehSum3 (fun a b c => B a b * D c b a c) := by
    calc
      _ = ehSum3 (fun a b c => B a b * D c a b c) := eh_sum3_rotate _
      _ = _ := by
        apply eh_sum3_congr
        intro a b c
        rw [ds c a b c]
  have h2 : ehSum3 (fun c a b => B a c * D b a b c) =
      ehSum3 (fun a b c => B a b * D c c a b) := by
    calc
      _ = ehSum3 (fun a b c => B a b * D c a c b) := eh_sum3_swap12 _
      _ = _ := by
        apply eh_sum3_congr
        intro a b c
        rw [ds c a c b]
  simp only [ehSum3,Finset.sum_sub_distrib,mul_sub] at h1 h2 ⊢
  rw [h1,h2]

theorem eh_weighted_divergence_expansion_algebra
    (v : ℝ) (B : Tensor2) (Γ Z : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (D : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum3 (fun c a b =>
      (v * ((∑ d : Fin 4, Γ d c d) * B a b -
        (∑ d : Fin 4, Γ a c d * B d b) -
        (∑ d : Fin 4, Γ b c d * B a d)) * Z c a b + v * B a b * D c a b c) -
      (v * ((∑ d : Fin 4, Γ d c d) * B a c -
        (∑ d : Fin 4, Γ a c d * B d c) -
        (∑ d : Fin 4, Γ c c d * B a d)) * Z b a b + v * B a c * D b a b c)) =
    v * (ehSum3 (fun c a b => B a b * D c a b c - B a c * D b a b c) +
      ehSum4 (fun c a b d =>
        Γ d c d * B a b * Z c a b - Γ a c d * B d b * Z c a b -
        Γ b c d * B a d * Z c a b - Γ d c d * B a c * Z b a b +
        Γ a c d * B d c * Z b a b + Γ c c d * B a d * Z b a b)) := by
  simp only [ehSum3,ehSum4,mul_add,mul_sub,
    Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    mul_left_comm,mul_comm]
  ring

end
end AASCSemanticExhaustion
