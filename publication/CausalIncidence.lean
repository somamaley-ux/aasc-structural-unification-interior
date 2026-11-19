import AccessDeletion

/-! The deletion theorem detects a bipartite matrix. For native event
preorders, all remaining comparisons and distinctness of the six underlying
events follow. For an arbitrary relation the two index families may overlap. -/
namespace AASCAccessDeletion

abbrev Role := Sum (Fin 3) (Fin 3)

/-- The full reflexive order of the standard example on three pairs. -/
def exampleOrder : Role → Role → Prop
  | .inl i, .inl j => i = j
  | .inr i, .inr j => i = j
  | .inl i, .inr j => i ≠ j
  | .inr _, .inl _ => False

private theorem thirdIndex (i j : Fin 3) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

/-- On the same native event carrier, the nine off-diagonal readings embed
the entire six-element order. Antisymmetry of the carrier is unnecessary. -/
theorem induced_example_of_six {E : Type*} [Preorder E]
    (six : Six ((· ≤ ·) : E → E → Prop)) :
    ∃ f : Role ↪ E, ∀ u v, f u ≤ f v ↔ exampleOrder u v := by
  obtain ⟨a, b, reads⟩ := six
  have launch (i j) : a i ≤ a j ↔ i = j := by
    refine ⟨?_, fun h => h ▸ le_rfl⟩
    intro h
    by_contra ne
    exact (reads i i).mp (h.trans ((reads j i).mpr (Ne.symm ne))) rfl
  have receive (i j) : b i ≤ b j ↔ i = j := by
    refine ⟨?_, fun h => h ▸ le_rfl⟩
    intro h
    by_contra ne
    exact (reads j j).mp (((reads j i).mpr (Ne.symm ne)).trans h) rfl
  have reverse (i j) : ¬ b i ≤ a j := by
    obtain ⟨k, ki, kj⟩ := thirdIndex i j
    intro h
    exact kj ((launch k j).mp (((reads k i).mpr ki).trans h))
  let g : Role → E := Sum.elim a b
  have exactOrder (u v : Role) : g u ≤ g v ↔ exampleOrder u v := by
    cases u with
    | inl i =>
      cases v with
      | inl j => exact launch i j
      | inr j => exact reads i j
    | inr i =>
      cases v with
      | inl j => exact ⟨reverse i j, False.elim⟩
      | inr j => exact receive i j
  have antisymmExample (u v : Role) :
      exampleOrder u v → exampleOrder v u → u = v := by
    cases u <;> cases v <;> simp [exampleOrder] <;> exact fun h _ => h
  have injective : Function.Injective g := by
    intro u v eq
    exact antisymmExample u v ((exactOrder u v).mp eq.le)
      ((exactOrder v u).mp eq.symm.le)
  exact ⟨⟨g, injective⟩, exactOrder⟩

/-- The geometric conclusion of the deletion theorem for a causal preorder. -/
theorem induced_example_iff_no_pair_basis {E : Type*} [Preorder E] :
    (∃ f : Role ↪ E, ∀ u v, f u ≤ f v ↔ exampleOrder u v) ↔
      ¬ PairBasis ((· ≤ ·) : E → E → Prop) := by
  rw [← six_iff_no_pair_basis]
  refine ⟨?_, induced_example_of_six⟩
  rintro ⟨f, h⟩
  exact ⟨fun i => f (.inl i), fun j => f (.inr j), fun i j => h (.inl i) (.inr j)⟩

/-- On just three underlying points the inequality relation realizes the
incidence matrix and fails pair sufficiency, despite no room for six events. -/
theorem three_point_incidence :
    Six ((· ≠ ·) : Fin 3 → Fin 3 → Prop) ∧
    ¬ PairBasis ((· ≠ ·) : Fin 3 → Fin 3 → Prop) ∧
    ¬ Nonempty (Role ↪ Fin 3) := by
  have matrix : Six ((· ≠ ·) : Fin 3 → Fin 3 → Prop) :=
    ⟨id, id, fun _ _ => Iff.rfl⟩
  refine ⟨matrix, (six_iff_no_pair_basis _).mp matrix, ?_⟩
  rintro ⟨f⟩
  have card := Fintype.card_le_of_injective f f.injective
  have impossible : ¬ Fintype.card Role ≤ Fintype.card (Fin 3) := by decide
  exact impossible card

end AASCAccessDeletion
