import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section
set_option maxHeartbeats 1000000
namespace AASCKleinGordon

theorem symmetric_complex_multilinear_diagonal_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ)
    (symmetric : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),B (fun i => v (σ i))=B v)
    (diagonal : ∀ x : E,B (fun _ => x)=0) : ∀ v,B v=0 := by
  intro v
  have hd : (fun x : E => B (fun _ => x))=0:=funext diagonal
  have h:=B.iteratedFDeriv_comp_diagonal (x:=0) v
  rw [hd] at h
  simp only [Pi.zero_def,iteratedFDeriv_zero_fun,Pi.zero_apply,ContinuousMultilinearMap.zero_apply,symmetric,
    Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)

end AASCKleinGordon
