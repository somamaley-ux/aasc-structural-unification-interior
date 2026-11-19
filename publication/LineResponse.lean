import LinePacket

namespace AASCLinePacket

def depleted : State → Prop
  | none => True
  | some (_,m) => m.card < 2

private theorem gate_depleted (g : Gate) (m : Mask) (h : m.card < 2) :
    (applyGate g m).card < 2 := by
  cases g with
  | pass => exact h
  | damage t => exact lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_left) h
  | repair => simp [applyGate, Nat.not_le_of_lt h]

theorem depleted_persists (cs : List Control) (s : State) (h : depleted s) :
    depleted (run cs s) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    cases s with
    | none => trivial
    | some v =>
      rcases v with ⟨p,m⟩
      unfold advance
      dsimp only
      split
      · exact gate_depleted _ m h
      · trivial

def FullSomewhere (s : State) : Prop := ∃ p : Site, s = some (p,full)

/-- Zero steps for an intact packet; exactly one suffices for every repairable
damage at every site; more severe damage cannot be compensated by any native
repair, routing, or state-dependent program of any length. -/
theorem correction_within_budget (p : Site) (m : Mask) (budget : ℕ) :
    (∃ cs : List Control, cs.length ≤ budget ∧ FullSomewhere (run cs (put p m))) ↔
      m=full ∨ (2 ≤ m.card ∧ 1 ≤ budget) := by
  constructor
  · rintro ⟨cs,len,where_,restored⟩
    by_cases mc : m.card < 2
    · have h : depleted (put p m) := by
        unfold put; split
        · exact mc
        · trivial
      have d := depleted_persists cs _ h
      rw [restored] at d
      norm_num [depleted,full] at d
    · by_cases nn : cs = []
      · subst cs
        unfold put at restored
        split at restored
        · exact Or.inl (congrArg Prod.snd (Option.some.inj restored))
        · contradiction
      · exact Or.inr ⟨by omega,le_trans (List.length_pos_iff.mpr nn) len⟩
  · rintro (rfl | ⟨mc,b⟩)
    · exact ⟨[],by simp,p,by simp [run,put,full]⟩
    · have hm : m.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨[repairStep .right], b,next .right p,by
        simp [run,put,advance,repairStep,applyGate,hm,mc,full]⟩

def march (dirs : List Dir) (p : Site) : Site := dirs.foldl (fun q d => next d q) p

private theorem clear_march (dirs : List Dir) (p : Site) :
    run (dirs.map drift) (some (p,full)) = some (march dirs p,full) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons d dirs ih =>
    change run _ (advance (drift d) _) = _
    have hd : advance (drift d) (some (p,full)) = some (next d p,full) := by
      simp [advance,drift,applyGate,full]
    rw [hd,ih]; rfl

/-- A prescribed nonempty path, including any turns, permits compensation
on the first step without consuming another transport tick. The threshold
is necessary even if all state-sensitive controllers and all paths are
allowed. -/
theorem repair_on_original_path (p : Site) (m : Mask) (d : Dir) (rest : List Dir) :
    run (repairStep d :: rest.map drift) (put p m) =
      if 2 ≤ m.card then some (march (d :: rest) p,full) else none := by
  by_cases hm : m.Nonempty
  · by_cases hc : 2 ≤ m.card
    · simp only [put,if_pos hm,if_pos hc]
      change run _ (advance (repairStep d) _) = _
      have ha : advance (repairStep d) (some (p,m)) = some (next d p,full) := by
        simp [advance,repairStep,applyGate,hc,full]
      rw [ha,clear_march]; rfl
    · simp only [put,if_pos hm,if_neg hc]
      change run _ (advance (repairStep d) _) = _
      have ha : advance (repairStep d) (some (p,m)) = none := by
        simp [advance,repairStep,applyGate,hc]
      rw [ha,no_recreation]
  · have em : m=∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    simp [em,put,no_recreation]

end AASCLinePacket
