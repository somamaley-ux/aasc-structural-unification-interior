import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-! The order-two instance of the algebraic Lovelock degree bound in four
dimensions. A component has five interchangeable pairs, each internally
symmetric. The cyclic identity is the remaining symmetry of Div². -/

namespace AASCSemanticExhaustion.Div2Four

abbrev Index := Fin 4
abbrev Pairs := Multiset (Sym2 Index)

/-- A single symmetric pair of coordinate indices. -/
def edge (a b : Index) : Pairs := {s(a, b)}

theorem edge_comm (a b : Index) : edge a b = edge b a := by
  unfold edge
  rw [Sym2.eq_swap (a := a) (b := b)]

/-- Package the five pairs of an arbitrary raw component. -/
def pairs : List (Index × Index) → Pairs
  | [] => 0
  | (a, b) :: rest => edge a b + pairs rest

@[simp] theorem card_edge (a b : Index) : (edge a b).card = 1 := by simp [edge]

@[simp] theorem card_pairs (l : List (Index × Index)) : (pairs l).card = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => rcases p with ⟨a,b⟩; simp [pairs, ih, Nat.add_comm]

/-- The three pairings of four adjacent indices sum to zero. The remaining
three symmetric pairs can be anywhere because pair order is immaterial. -/
def Cyclic (T : Pairs → ℝ) : Prop :=
  ∀ (a b c d : Index) (r : Pairs), r.card = 3 →
    T (edge a b + edge c d + r) + T (edge b c + edge a d + r) +
      T (edge c a + edge b d + r) = 0

private theorem double_and_single_zero {T : Pairs → ℝ} (h : Cyclic T)
    (a b : Index) (r : Pairs) (hr : r.card = 3) :
    T (edge a a + edge a b + r) = 0 := by
  have hc := h a a a b r hr
  linarith

private theorem three_singles_zero {T : Pairs → ℝ} (h : Cyclic T)
    (a b c d : Index) (r : Pairs) (hr : r.card = 2) :
    T (edge a b + edge a c + edge a d + r) = 0 := by
  have hc := h a b a c (edge a d + r) (by simp [hr])
  have hz := double_and_single_zero h a d (edge b c + r) (by simp [hr])
  rw [edge_comm b a] at hc
  have eqz : edge a a + edge b c + (edge a d + r) =
      edge a a + edge a d + (edge b c + r) := by simp only [add_assoc, add_left_comm, add_comm]
  rw [eqz, hz] at hc
  rw [show edge a b + edge a c + edge a d + r =
      edge a b + edge a c + (edge a d + r) by simp only [add_assoc, add_left_comm, add_comm]]
  linarith

private def occurrences (a : Index) : List (Index × Index) → ℕ
  | [] => 0
  | (b,c) :: xs =>
    (if b = a then 1 else 0) + (if c = a then 1 else 0) + occurrences a xs

private theorem occurrences_sum (xs : List (Index × Index)) :
    (∑ a, occurrences a xs) = 2 * xs.length := by
  induction xs with
  | nil => simp [occurrences]
  | cons p xs ih =>
    rcases p with ⟨b,c⟩
    simp [occurrences, Finset.sum_add_distrib, ih]
    omega

private def stars (a : Index) : List Index → Pairs
  | [] => 0
  | b :: ns => edge a b + stars a ns

private theorem split_at_index (a : Index) (xs : List (Index × Index)) :
    ∃ (k : ℕ) (ns : List Index) (r : Pairs),
      pairs xs = k • edge a a + stars a ns + r ∧
      occurrences a xs = 2 * k + ns.length := by
  induction xs with
  | nil => exact ⟨0, [], 0, by simp [pairs, stars], rfl⟩
  | cons p xs ih =>
    rcases p with ⟨b,c⟩
    obtain ⟨k, ns, r, hp, hn⟩ := ih
    by_cases hb : b = a <;> by_cases hc : c = a
    · subst b; subst c
      refine ⟨k+1,ns,r,?_,?_⟩
      · simp only [pairs, hp, add_nsmul, one_nsmul]; simp only [add_assoc, add_left_comm, add_comm]
      · simp [occurrences, hn]; omega
    · subst b
      refine ⟨k,c :: ns,r,?_,?_⟩
      · simp only [pairs, hp, stars]; simp only [add_left_comm, add_comm]
      · simp [occurrences, hc, hn]; omega
    · subst c
      refine ⟨k,b :: ns,r,?_,?_⟩
      · simp only [pairs, hp, stars]; rw [edge_comm b a]; simp only [add_left_comm, add_comm]
      · simp [occurrences, hb, hn]; omega
    · refine ⟨k,ns,edge b c + r,?_,?_⟩
      · simp only [pairs, hp]; simp only [add_assoc, add_left_comm, add_comm]
      · simp [occurrences, hb, hc, hn]

/-- Every five-pair component of a Div² tensor vanishes in dimension four.
The ten slots contain some coordinate at least three times. Either two occur
in the same pair, or cyclicity converts two single occurrences into that case. -/
theorem component_zero (T : Pairs → ℝ) (h : Cyclic T)
    (xs : List (Index × Index)) (hxs : xs.length = 5) : T (pairs xs) = 0 := by
  have repeated : ∃ a, 3 ≤ occurrences a xs := by
    by_contra! hr
    have bound : (∑ a, occurrences a xs) ≤ ∑ _ : Index, 2 :=
      Finset.sum_le_sum (fun a _ => by have := hr a; omega)
    rw [occurrences_sum, hxs] at bound
    norm_num at bound
  obtain ⟨a, ha⟩ := repeated
  obtain ⟨k, ns, r, hp, hn⟩ := split_at_index a xs
  have hcard : (pairs xs).card = 5 := by simp [hxs]
  cases k with
  | zero =>
    cases ns with
    | nil => simp at hn; omega
    | cons b ns =>
      cases ns with
      | nil => simp at hn; omega
      | cons c ns =>
        cases ns with
        | nil => simp at hn; omega
        | cons d ns =>
          have he : pairs xs = edge a b + edge a c + edge a d + (stars a ns + r) := by
            rw [hp]; simp only [zero_nsmul, zero_add, stars]; simp only [add_assoc, add_left_comm, add_comm]
          rw [he] at hcard ⊢
          apply three_singles_zero h
          simp only [Multiset.card_add, card_edge] at hcard ⊢
          omega
  | succ k =>
    cases ns with
    | cons b ns =>
      have he : pairs xs = edge a a + edge a b + (k • edge a a + stars a ns + r) := by
        rw [hp]; simp only [succ_nsmul, stars]; simp only [add_assoc, add_left_comm, add_comm]
      rw [he] at hcard ⊢
      apply double_and_single_zero h
      simp only [Multiset.card_add, card_edge] at hcard ⊢
      omega
    | nil =>
      cases k with
      | zero => simp at hn; omega
      | succ k =>
        have he : pairs xs = edge a a + edge a a + (k • edge a a + r) := by
          rw [hp]; simp only [succ_nsmul, stars, add_zero]; simp only [add_assoc, add_left_comm, add_comm]
        rw [he] at hcard ⊢
        apply double_and_single_zero h
        simp only [Multiset.card_add, card_edge] at hcard ⊢
        omega

#print axioms component_zero
end AASCSemanticExhaustion.Div2Four
