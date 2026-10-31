import KGSchwartzCoordinates
import Mathlib.GroupTheory.Perm.Fin

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

def swapDelete (n : ℕ) (i : Fin (n+1)) (y : ParticleConfiguration (n+1)) :
    ParticleConfiguration n := fun j => y (Equiv.swap 0 i j.succ)

theorem symmetrizer_insert_decompose (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz n) (y : ParticleConfiguration (n+1)) :
    schwartzSymmetrizer (n+1) (particleTensorInsertCLM n f H.val) y =
      permutationAverageCoefficient (n+1) * (Fintype.card (Equiv.Perm (Fin n)) : ℂ) *
        ∑ i : Fin (n+1), f (y i) * H.val (swapDelete n i y) := by
  rw [schwartzSymmetrizer_apply]
  have hsum : (∑ σ : Equiv.Perm (Fin (n+1)),
      particleTensorInsertCLM n f H.val (fun i => y (σ i))) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ) *
        ∑ i : Fin (n+1), f (y i) * H.val (swapDelete n i y) := by
    rw [← (Equiv.Perm.decomposeFin (n:=n)).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    have hterm (i : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
        particleTensorInsertCLM n f H.val
          (fun j => y (Equiv.Perm.decomposeFin.symm (i,σ) j)) =
          f (y i) * H.val (swapDelete n i y) := by
      rw [particleTensorInsertCLM_apply, Equiv.Perm.decomposeFin_symm_apply_zero]
      congr 1
      have he : Fin.tail (fun j => y (Equiv.Perm.decomposeFin.symm (i,σ) j)) =
          fun j => swapDelete n i y (σ j) := by
        funext j
        exact congrArg y (Equiv.Perm.decomposeFin_symm_apply_succ σ i j)
      rw [he, H.property σ]
    simp_rw [hterm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum]
  ring

theorem symmetrizer_insert_apply (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz n) (y : ParticleConfiguration (n+1)) :
    schwartzSymmetrizer (n+1) (particleTensorInsertCLM n f H.val) y =
      ((n+1 : ℕ) : ℂ)⁻¹ * ∑ i : Fin (n+1), f (y i) * H.val (swapDelete n i y) := by
  rw [symmetrizer_insert_decompose]
  congr 1
  simp only [permutationAverageCoefficient, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]
  push_cast
  have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp

end AASCKleinGordon
