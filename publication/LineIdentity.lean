import LinePacket

namespace AASCLinePacket

def place (p u : Site) : Site := (p.1+u.1,p.2+u.2)
def relative (p q : Site) : Site := (q.1-p.1,q.2-p.2)
def placeState (p : Site) : State → State
  | none => none
  | some (q,m) => some (place p q,m)

def placeControl (p : Site) (c : Control) : Control :=
  fun q m => c (relative p q) m

private theorem unplace (p q : Site) : relative p (place p q) = q := by
  rcases p with ⟨u,v⟩; rcases q with ⟨x,y⟩; simp [relative,place]

private theorem next_place (p q : Site) (d : Dir) : next d (place p q) = place p (next d q) := by
  rcases p with ⟨u,v⟩; rcases q with ⟨x,y⟩; cases d <;> simp [next,place,Nat.add_assoc]

private theorem step_at (p : Site) (c : Control) (s : State) :
    advance (placeControl p c) (placeState p s) = placeState p (advance c s) := by
  cases s with
  | none => rfl
  | some v =>
    rcases v with ⟨q,m⟩
    simp only [placeState,advance,placeControl,unplace,next_place]
    split <;> rfl

theorem transported_local_operation (p : Site) (cs : List Control) (s : State) :
    run (cs.map (placeControl p)) (placeState p s) = placeState p (run cs s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    change run _ (advance (placeControl p c) _) = _
    rw [step_at,ih]; rfl

theorem transported_local_observation (p q : Site) (s : State) :
    observe (place p q) (placeState p s) = observe q s := by
  cases s with
  | none => rfl
  | some v =>
    rcases v with ⟨r,m⟩
    have inj : place p q = place p r ↔ q = r :=
      ⟨fun h => by simpa only [unplace] using congrArg (relative p) h,fun h => h ▸ rfl⟩
    simp only [placeState,observe,inj]

/-- Compare moving the same intact original to two different occupied ports.
Each future reader and controller is transported to the corresponding
relative port, and may depend on the locally observed mask. Past fixed
verdicts, the original event addresses and unmatched detectors retain
their distinct meanings. -/
theorem full_future_at_two_ports (p q detector : Site) (cs : List Control) :
    observe (place p detector) (run (cs.map (placeControl p)) (some (p,full))) =
      observe (place q detector) (run (cs.map (placeControl q)) (some (q,full))) := by
  have h (k : Site) : some (k,full) = placeState k initial := by simp [placeState,initial,place]
  rw [h p,h q,transported_local_operation,transported_local_operation,
      transported_local_observation,transported_local_observation]

end AASCLinePacket
