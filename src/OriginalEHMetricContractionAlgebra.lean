import OriginalEHPalatiniContractionAlgebra

/-! Index placement and normalization algebra for the independently
computed density variation. These are finite matrix identities. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators

theorem eh_sum4_exchange_pairs (F : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ehSum4 F = ehSum4 (fun a b c d => F c d a b) := by
  calc
    _ = ehSum4 (fun a b c d => F d a b c) := eh_sum4_reindex_4123 F
    _ = ehSum4 (fun a b c d => F c d a b) :=
      eh_sum4_reindex_4123 (fun a b c d => F d a b c)

theorem eh_matrix_inverse_variation_contraction (B H R : Tensor2)
    (bs : ∀ a b, B a b = B b a) :
    (∑ a : Fin 4, ∑ b : Fin 4, (-B * H * B) a b * R a b) =
      -(∑ a : Fin 4, ∑ b : Fin 4, (B * R * B) a b * H a b) := by
  have h : ehSum4 (fun a b i j => B a i * H i j * B j b * R a b) =
      ehSum4 (fun i j a b => B i a * R a b * B b j * H i j) := by
    calc
      _ = ehSum4 (fun i j a b => B a i * H i j * B j b * R a b) :=
        eh_sum4_exchange_pairs _
      _ = _ := by
        apply eh_sum4_congr
        intro i j a b
        rw [bs a i,bs j b]
        ring
  simp only [Matrix.mul_apply,Matrix.neg_apply,Finset.sum_mul,
    neg_mul,Finset.sum_neg_distrib]
  apply congrArg Neg.neg
  change ehSum4 (fun a b j i => B a i * H i j * B j b * R a b) = _
  calc
    _ = ehSum4 (fun a b i j => B a i * H i j * B j b * R a b) := eh_sum4_swap34 _
    _ = _ := h
    _ = ehSum4 (fun i j b a => B i a * R a b * B b j * H i j) := eh_sum4_swap34 _

theorem eh_matrix_trace_symmetric_contraction (B H : Tensor2)
    (hs : ∀ a b, H a b = H b a) :
    Matrix.trace (B * H) = ∑ a : Fin 4, ∑ b : Fin 4, B a b * H a b := by
  change (∑ a : Fin 4, ∑ b : Fin 4, B a b * H b a) = _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hs b a]

theorem eh_einstein_matrix_contraction (B G R H : Tensor2) (s Λ : ℝ)
    (bg : B * G = 1) :
    (∑ a : Fin 4, ∑ b : Fin 4,
      (B * (R - (s/2) • G + Λ • G) * B) a b * H a b) =
      (∑ a : Fin 4, ∑ b : Fin 4, (B * R * B) a b * H a b) +
        (Λ-s/2) * (∑ a : Fin 4, ∑ b : Fin 4, B a b * H a b) := by
  have norm : B * (R - (s/2) • G + Λ • G) * B =
      B * R * B - (s/2) • B + Λ • B := by
    simp only [mul_add,mul_sub,add_mul,sub_mul,mul_smul_comm,smul_mul_assoc]
    rw [bg,one_mul]
  rw [norm]
  change (∑ a : Fin 4, ∑ b : Fin 4,
    ((B * R * B) a b - (s/2) * B a b + Λ * B a b) * H a b) = _
  simp only [add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.mul_sum,mul_assoc]
  ring

end
end AASCSemanticExhaustion
