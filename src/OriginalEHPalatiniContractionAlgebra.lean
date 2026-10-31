import OriginalEHCompactBoundaryIBP

/-! Finite contraction algebra for the actual Palatini calculation.
Only the displayed lower-slot symmetries occur as algebraic premises. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators

def ehSum4 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, F a b c d

theorem eh_sum4_congr (F G : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ a b c d, F a b c d = G a b c d) : ehSum4 F = ehSum4 G := by
  simp only [ehSum4]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  exact h a b c d

theorem eh_sum4_swap12 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F b a c d) := by
  unfold ehSum4
  exact Finset.sum_comm

theorem eh_sum4_swap23 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F a c b d) := by
  unfold ehSum4
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem eh_sum4_swap34 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F a b d c) := by
  unfold ehSum4
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

theorem eh_sum4_reindex_4123 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F d a b c) := by
  calc
    ehSum4 F = ehSum4 (fun a b c d => F b a c d) := eh_sum4_swap12 F
    _ = ehSum4 (fun a b c d => F c a b d) := eh_sum4_swap23 (fun a b c d => F b a c d)
    _ = ehSum4 (fun a b c d => F d a b c) := eh_sum4_swap34 (fun a b c d => F c a b d)

theorem eh_sum4_reindex_3421 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F c d b a) := by
  calc
    ehSum4 F = ehSum4 (fun a b c d => F a c b d) := eh_sum4_swap23 F
    _ = ehSum4 (fun a b c d => F b c a d) := eh_sum4_swap12 (fun a b c d => F a c b d)
    _ = ehSum4 (fun a b c d => F b d a c) := eh_sum4_swap34 (fun a b c d => F b c a d)
    _ = ehSum4 (fun a b c d => F c d a b) := eh_sum4_swap23 (fun a b c d => F b d a c)
    _ = ehSum4 (fun a b c d => F c d b a) := eh_sum4_swap12 (fun a b c d => F c d a b)

theorem eh_sum4_reindex_4132 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F d a c b) := by
  calc
    ehSum4 F = ehSum4 (fun a b c d => F b a c d) := eh_sum4_swap12 F
    _ = ehSum4 (fun a b c d => F c a b d) := eh_sum4_swap23 (fun a b c d => F b a c d)
    _ = ehSum4 (fun a b c d => F d a b c) := eh_sum4_swap34 (fun a b c d => F c a b d)
    _ = ehSum4 (fun a b c d => F d a c b) := eh_sum4_swap23 (fun a b c d => F d a b c)

theorem eh_sum4_reindex_2431 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F b d c a) := by
  calc
    ehSum4 F = ehSum4 (fun a b c d => F a c b d) := eh_sum4_swap23 F
    _ = ehSum4 (fun a b c d => F a d b c) := eh_sum4_swap34 (fun a b c d => F a c b d)
    _ = ehSum4 (fun a b c d => F a d c b) := eh_sum4_swap23 (fun a b c d => F a d b c)
    _ = ehSum4 (fun a b c d => F b d c a) := eh_sum4_swap12 (fun a b c d => F a d c b)

theorem eh_sum4_reindex_4231 (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F d b c a) := by
  calc
    ehSum4 F = ehSum4 (fun a b c d => F b a c d) := eh_sum4_swap12 F
    _ = ehSum4 (fun a b c d => F c a b d) := eh_sum4_swap23 (fun a b c d => F b a c d)
    _ = ehSum4 (fun a b c d => F d a b c) := eh_sum4_swap34 (fun a b c d => F c a b d)
    _ = ehSum4 (fun a b c d => F d a c b) := eh_sum4_swap23 (fun a b c d => F d a b c)
    _ = ehSum4 (fun a b c d => F d b c a) := eh_sum4_swap12 (fun a b c d => F d a c b)

theorem eh_palatini_weighted_connection_algebra
    (B : Tensor2) (Γ Z : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (gs : ∀ a b c, Γ a b c = Γ a c b)
    (zs : ∀ a b c, Z a b c = Z a c b) :
    ehSum4 (fun c a b d =>
      Γ d c d * B a b * Z c a b - Γ a c d * B d b * Z c a b -
      Γ b c d * B a d * Z c a b - Γ d c d * B a c * Z b a b +
      Γ a c d * B d c * Z b a b + Γ c c d * B a d * Z b a b) =
    ehSum4 (fun a b c d => B a b *
      (Z c c d * Γ d b a + Γ c c d * Z d b a -
        Z c b d * Γ d c a - Γ c b d * Z d c a)) := by
  have h1 : ehSum4 (fun c a b d => Γ d c d * B a b * Z c a b) =
      ehSum4 (fun a b c d => B a b * (Γ c c d * Z d b a)) := by
    calc
      _ = ehSum4 (fun a b c d => Γ c d c * B a b * Z d a b) := eh_sum4_reindex_4123 _
      _ = _ := by
        apply eh_sum4_congr
        intro a b c d
        rw [gs c d c,zs d a b]
        ring
  have h2 : ehSum4 (fun c a b d => Γ a c d * B d b * Z c a b) =
      ehSum4 (fun a b c d => B a b * (Z c b d * Γ d c a)) := by
    calc
      _ = ehSum4 (fun a b c d => Γ d c a * B a b * Z c d b) := eh_sum4_reindex_3421 _
      _ = _ := by
        apply eh_sum4_congr
        intro a b c d
        rw [zs c d b]
        ring
  have h3 : ehSum4 (fun c a b d => Γ b c d * B a d * Z c a b) =
      ehSum4 (fun a b c d => B a b * (Γ c b d * Z d c a)) := by
    calc
      _ = ehSum4 (fun a b c d => Γ c d b * B a b * Z d a c) := eh_sum4_reindex_4132 _
      _ = _ := by
        apply eh_sum4_congr
        intro a b c d
        rw [gs c d b,zs d a c]
        ring
  have h4 : ehSum4 (fun c a b d => Γ a c d * B d c * Z b a b) =
      ehSum4 (fun a b c d => B a b * (Z c c d * Γ d b a)) := by
    calc
      _ = ehSum4 (fun a b c d => Γ d b a * B a b * Z c d c) := eh_sum4_reindex_2431 _
      _ = _ := by
        apply eh_sum4_congr
        intro a b c d
        rw [zs c d c]
        ring
  have h5 : ehSum4 (fun c a b d => Γ c c d * B a d * Z b a b) =
      ehSum4 (fun c a b d => Γ d c d * B a c * Z b a b) := by
    calc
      _ = ehSum4 (fun c a b d => Γ d d c * B a c * Z b a b) := eh_sum4_reindex_4231 _
      _ = _ := by
        apply eh_sum4_congr
        intro c a b d
        rw [gs d d c]
  simp only [mul_add,mul_sub,ehSum4,Finset.sum_add_distrib,Finset.sum_sub_distrib] at h1 h2 h3 h4 h5 ⊢
  rw [h1,h2,h3,h4,h5]
  ring

end
end AASCSemanticExhaustion
