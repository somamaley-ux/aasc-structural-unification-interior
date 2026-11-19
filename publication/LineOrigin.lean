import LinePacket

namespace AASCLinePacket

def validState : State → Prop
  | none => True
  | some (_,m) => m.Nonempty

private theorem valid_advance (c : Control) (s : State) : validState (advance c s) := by
  cases s with
  | none => trivial
  | some v =>
    rcases v with ⟨p,m⟩
    simp only [advance]
    split
    · assumption
    · trivial

private theorem valid_run (cs : List Control) (s : State) (h : validState s) :
    validState (run cs s) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (valid_advance c s)

/-- Every prior cut of a successful experiment contains precisely one
surviving packet, on the actual common prefix. There is no origin identifier
or conserved hidden tag in the state. -/
theorem occupied_prefix_unique (pre post : List Control) (q : Site) (m : Mask)
    (ended : run (pre ++ post) initial = some (q,m)) :
    ∃! w : Site × Mask, run pre initial = some w ∧ w.2.Nonempty := by
  have eq : run post (run pre initial) = some (q,m) := by
    simpa [run,List.foldl_append] using ended
  cases e : run pre initial with
  | none => rw [e,no_recreation] at eq; contradiction
  | some w =>
    have v := valid_run pre initial (by simp [validState,initial,full])
    rw [e] at v
    exact ⟨w,⟨rfl,v⟩,fun w' a => (Option.some.inj a.1).symm⟩

/-- A matched failed prefix is absorbing, including under later native
repair and steering. -/
theorem extinct_prefix_irreversible (pre post : List Control)
    (gone : run pre initial = none) : run (pre ++ post) initial = none := by
  change List.foldl _ _ _ = _
  rw [List.foldl_append]
  change run post (run pre initial) = _
  rw [gone,no_recreation]

end AASCLinePacket
