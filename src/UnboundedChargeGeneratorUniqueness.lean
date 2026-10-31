import ObservableVacuumUniqueness
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Exact domain-sensitive generator uniqueness after the manuscript's
observable/vacuum argument. Generators are partial linear maps on actual
domains, not bounded operators on the entire Hilbert space. The general
theorem's representation and exact generator hypotheses remain explicit;
their construction on the free Fock carrier is a further task. -/
noncomputable section
namespace AASCKleinGordon
namespace GlobalCharge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ExactGenerator (κ : ℂ) (U : ℝ → H ≃ₗᵢ[ℂ] H) (Q : H →ₗ.[ℂ] H) : Prop :=
  (∀ x, DifferentiableAt ℝ (fun t => U t x) 0 ↔ x ∈ Q.domain) ∧
  (∀ x : Q.domain, HasDerivAt (fun t => U t x.val) (κ • Q x) 0)

theorem exact_unbounded_generator_unique
    (κ : ℂ) (hκ : κ≠0)
    (U V : ℝ → H ≃ₗᵢ[ℂ] H) (Q P : H →ₗ.[ℂ] H)
    (hQ : ExactGenerator κ U Q) (hP : ExactGenerator κ V P)
    (groups_equal : ∀ t x,U t x=V t x) : Q=P := by
  have huv : U=V := by funext t; ext x; exact groups_equal t x
  subst V
  have hd : Q.domain=P.domain := by
    ext x
    exact (hQ.1 x).symm.trans (hP.1 x)
  apply LinearPMap.ext hd
  intro x hx hy
  have h := (hQ.2 ⟨x,hx⟩).unique (hP.2 ⟨x,hy⟩)
  exact (smul_right_injective H hκ) h

theorem global_observable_vacuum_unbounded_charge_equality
    (κ : ℂ) (hκ : κ≠0)
    (O : Subalgebra ℂ (H →L[ℂ] H)) (hirr : ObservableIrreducible O)
    (Ω : H) (hΩ : Ω≠0) (U V : ℝ → H ≃ₗᵢ[ℂ] H)
    (same : ∀ t,∀ A : O,∀ x,U t (A.val ((U t).symm x))=V t (A.val ((V t).symm x)))
    (vacU : ∀ t,U t Ω=Ω) (vacV : ∀ t,V t Ω=Ω)
    (Q P : H →ₗ.[ℂ] H) (hQ : ExactGenerator κ U Q) (hP : ExactGenerator κ V P) :
    (∀ t x,U t x=V t x) ∧ Q=P := by
  have groups : ∀ t x,U t x=V t x := by
    intro t
    exact same_observable_automorphisms_and_vacuum_force_unitary_equality O hirr Ω hΩ
      (U t) (V t) (same t) (vacU t) (vacV t)
  exact ⟨groups,exact_unbounded_generator_unique κ hκ U V Q P hQ hP groups⟩

theorem physical_generator_coefficient_nonzero (hbar : ℝ) (hbar_pos : 0<hbar) :
    (-Complex.I/(hbar : ℂ))≠0 := by
  apply div_ne_zero (by simp)
  exact_mod_cast ne_of_gt hbar_pos

end GlobalCharge
end AASCKleinGordon
