import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Data.Complex.Basic

namespace AASCKleinGordon

theorem algebra_adjoin_star_mem {A : Type*} [Semiring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (s : Set A)
    (hs : ∀ x∈s,star x∈Algebra.adjoin ℂ s)
    {x : A} (hx : x∈Algebra.adjoin ℂ s) : star x∈Algebra.adjoin ℂ s := by
  induction hx using Algebra.adjoin_induction with
  | mem x h => exact hs x h
  | algebraMap z =>
      rw [← algebraMap_star_comm]
      exact (Algebra.adjoin ℂ s).algebraMap_mem (star z)
  | add x y _ _ hx hy =>
      rw [star_add]
      exact (Algebra.adjoin ℂ s).add_mem hx hy
  | mul x y _ _ hx hy =>
      rw [star_mul]
      exact (Algebra.adjoin ℂ s).mul_mem hy hx

end AASCKleinGordon
