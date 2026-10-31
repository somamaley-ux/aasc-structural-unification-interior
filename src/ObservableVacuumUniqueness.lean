import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.Basic

/-! Current Module B section6: observable-algebra irreducibility and an
invariant vacuum remove the relative commutant. The cyclic-vacuum argument
below proves that step without assuming charge matrix matching or bounded
generators. Actual Fock observable irreducibility remains to be constructed. -/
noncomputable section
namespace AASCKleinGordon
namespace GlobalCharge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def ObservableIrreducible (O : Subalgebra ℂ (H →L[ℂ] H)) : Prop :=
  ∀ W : Submodule ℂ H, IsClosed (W : Set H) →
    (∀ A : O, ∀ x ∈ W, A.val x ∈ W) → W=⊥ ∨ W=⊤

def vacuumOrbitSpan (O : Subalgebra ℂ (H →L[ℂ] H)) (Ω : H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range (fun A : O => A.val Ω))

theorem vacuum_mem_orbitSpan (O : Subalgebra ℂ (H →L[ℂ] H)) (Ω : H) :
    Ω ∈ vacuumOrbitSpan O Ω := by
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

theorem orbitSpan_invariant (O : Subalgebra ℂ (H →L[ℂ] H)) (Ω : H) (A : O) :
    ∀ x ∈ vacuumOrbitSpan O Ω, A.val x ∈ vacuumOrbitSpan O Ω := by
  intro x hx
  change x ∈ (vacuumOrbitSpan O Ω).comap A.val.toLinearMap
  apply (Submodule.span_le.mpr ?_) hx
  rintro z ⟨B,rfl⟩
  apply Submodule.subset_span
  exact ⟨A*B,rfl⟩

theorem orbitClosure_invariant (O : Subalgebra ℂ (H →L[ℂ] H)) (Ω : H) (A : O) :
    ∀ x ∈ (vacuumOrbitSpan O Ω).topologicalClosure,
      A.val x ∈ (vacuumOrbitSpan O Ω).topologicalClosure := by
  intro x hx
  have hc : IsClosed {x | A.val x ∈ (vacuumOrbitSpan O Ω).topologicalClosure} :=
    (vacuumOrbitSpan O Ω).isClosed_topologicalClosure.preimage A.val.continuous
  apply closure_minimal ?_ hc hx
  intro y hy
  exact (vacuumOrbitSpan O Ω).le_topologicalClosure (orbitSpan_invariant O Ω A y hy)

theorem irreducible_nonzero_vacuum_is_cyclic
    (O : Subalgebra ℂ (H →L[ℂ] H)) (hirr : ObservableIrreducible O)
    (Ω : H) (hΩ : Ω≠0) : (vacuumOrbitSpan O Ω).topologicalClosure=⊤ := by
  rcases hirr _ (vacuumOrbitSpan O Ω).isClosed_topologicalClosure (orbitClosure_invariant O Ω) with h|h
  · have hm := (vacuumOrbitSpan O Ω).le_topologicalClosure (vacuum_mem_orbitSpan O Ω)
    rw [h] at hm
    exact (hΩ hm).elim
  · exact h

theorem commuting_unitary_fixing_cyclic_vacuum_is_identity
    (O : Subalgebra ℂ (H →L[ℂ] H)) (Ω : H)
    (cyclic : (vacuumOrbitSpan O Ω).topologicalClosure=⊤)
    (W : H ≃ₗᵢ[ℂ] H)
    (commutes : ∀ A : O, ∀ x, W (A.val x)=A.val (W x)) (fixed : W Ω=Ω) :
    ∀ x, W x=x := by
  let K : Submodule ℂ H := (W.toLinearIsometry.toContinuousLinearMap-ContinuousLinearMap.id ℂ H).ker
  have hk : IsClosed (K : Set H) := ContinuousLinearMap.isClosed_ker _
  have hs : vacuumOrbitSpan O Ω ≤ K := by
    apply Submodule.span_le.mpr
    rintro z ⟨A,rfl⟩
    change W (A.val Ω)-A.val Ω=0
    rw [commutes,fixed,sub_self]
  have hclosed : (vacuumOrbitSpan O Ω).topologicalClosure ≤ K := by
    exact closure_minimal hs hk
  rw [cyclic] at hclosed
  intro x
  have hx := hclosed (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ H))
  change W x-x=0 at hx
  exact sub_eq_zero.mp hx

theorem same_observable_automorphisms_and_vacuum_force_unitary_equality
    (O : Subalgebra ℂ (H →L[ℂ] H)) (hirr : ObservableIrreducible O)
    (Ω : H) (hΩ : Ω≠0) (U V : H ≃ₗᵢ[ℂ] H)
    (same : ∀ A : O, ∀ x, U (A.val (U.symm x))=V (A.val (V.symm x)))
    (hU : U Ω=Ω) (hV : V Ω=Ω) : ∀ x,U x=V x := by
  let W := U.trans V.symm
  have comm : ∀ A : O,∀ x,W (A.val x)=A.val (W x) := by
    intro A x
    have h := congrArg V.symm (same A (U x))
    simpa [W] using h
  have fix : W Ω=Ω := by
    change V.symm (U Ω)=Ω
    rw [hU]
    have h := congrArg V.symm hV
    simpa using h.symm
  have hid := commuting_unitary_fixing_cyclic_vacuum_is_identity O Ω
    (irreducible_nonzero_vacuum_is_cyclic O hirr Ω hΩ) W comm fix
  intro x
  have h := congrArg V (hid x)
  simpa [W] using h

end GlobalCharge
end AASCKleinGordon
