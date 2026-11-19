import LinePacket

/-! The sparse packet step has an equivalent local field realization. At a
site q each lane is present after an update exactly when an incoming
nearest-neighbour link delivered it. The observables at all original cells
separate reachable sparse states, including their current damage masks. -/
namespace AASCLineFieldBridge
open AASCLinePacket

abbrev Field := Site → Mask
def Incoming (p q : Site) : Prop := next .right p = q ∨ next .left p = q

def delivered (c : Control) (f : Field) (q : Site) (i : Lane) : Prop :=
  ∃ p, next (c p (f p)).2 p = q ∧ i ∈ applyGate (c p (f p)).1 (f p)

theorem empty_stays_empty (g : Gate) : applyGate g ∅ = ∅ := by
  cases g <;> simp [applyGate]

private theorem occupied_step_test (p q : Site) (m : Mask) (c : Control) (i : Lane) :
    i ∈ observe q (advance c (some (p,m))) ↔
      next (c p m).2 p = q ∧ i ∈ applyGate (c p m).1 m := by
  by_cases live : (applyGate (c p m).1 m).Nonempty
  · by_cases arrives : next (c p m).2 p = q
    · simp [advance,observe,live,arrives]
    · simp [advance,observe,live,arrives,Ne.symm arrives]
  · have killed := Finset.not_nonempty_iff_eq_empty.mp live
    simp [advance,observe,killed]

/-- Update by the sparse machine is exactly delivery by the field rule. -/
theorem field_step_exact (c : Control) (s : State) (q : Site) (i : Lane) :
    i ∈ observe q (advance c s) ↔ delivered c (fun p => observe p s) q i := by
  cases s with
  | none => simp [advance,observe,delivered,empty_stays_empty]
  | some pm =>
    obtain ⟨p,m⟩ := pm
    rw [occupied_step_test]
    constructor
    · rintro ⟨arrive,present⟩
      exact ⟨p,by simpa [observe] using arrive,by simpa [observe] using present⟩
    · rintro ⟨r,arrive,present⟩
      by_cases source : r = p
      · subst r
        exact ⟨by simpa [observe] using arrive,by simpa [observe] using present⟩
      · simp [observe,source,empty_stays_empty] at present

/-- No delivery can depend on a cell outside the two possible input links. -/
theorem field_update_local (q : Site) (i : Lane) (f g : Field) (c d : Control)
    (same : ∀ p, Incoming p q → f p = g p ∧ c p (f p) = d p (g p)) :
    delivered c f q i ↔ delivered d g q i := by
  have inputs (dir : Dir) (p : Site) (arrive : next dir p = q) : Incoming p q := by
    cases dir with
    | right => exact Or.inl arrive
    | left  => exact Or.inr arrive
  constructor
  · rintro ⟨p,arrive,live⟩
    obtain ⟨sameMask,sameGate⟩ := same p (inputs _ _ arrive)
    have h := congrArg₂ applyGate (congrArg Prod.fst sameGate) sameMask
    exact ⟨p,by rwa [← sameGate],h ▸ live⟩
  · rintro ⟨p,arrive,live⟩
    obtain ⟨sameMask,sameGate⟩ := same p (inputs _ _ arrive)
    have h := congrArg₂ applyGate (congrArg Prod.fst sameGate) sameMask
    exact ⟨p,by rwa [sameGate],h.symm ▸ live⟩

def wellFormed : State → Prop
  | none => True
  | some (_,m) => m.Nonempty

theorem step_wellFormed (c : Control) (s : State) : wellFormed (advance c s) := by
  cases s with
  | none => trivial
  | some pm =>
    obtain ⟨p,m⟩ := pm
    unfold advance
    dsimp only
    split
    · assumption
    · trivial

/-- The complete set of original cell readings retains the actual current
state. Losing a lane cannot be identified with full health at fixed probes. -/
theorem cell_readings_separate {s t : State} (hs : wellFormed s) (ht : wellFormed t)
    (eq : ∀ p, observe p s = observe p t) : s = t := by
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some qm =>
      obtain ⟨q,m⟩ := qm
      exact False.elim (ht.ne_empty (by simpa [observe] using (eq q).symm))
  | some pm =>
    obtain ⟨p,m⟩ := pm
    cases t with
    | none => exact False.elim (hs.ne_empty (by simpa [observe] using eq p))
    | some qn =>
      obtain ⟨q,n⟩ := qn
      by_cases site : p = q
      · subst q
        have h : m = n := by simpa [observe] using eq p
        rw [h]
      · exact False.elim (hs.ne_empty (by simpa [observe,site] using eq p))

/-- This originally empty local domain can actually be probed in the same
single-launch domain. Routing the existing input through the other exit
leaves the chosen receiver empty. -/
theorem empty_cell_receives_original :
    let q := next .right (0,0)
    observe q initial = ∅ ∧
    observe q (advance (drift .right) initial) = full ∧
    observe q (advance (drift .left) initial) = ∅ := by decide

end AASCLineFieldBridge
