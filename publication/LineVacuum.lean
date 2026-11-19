import LinePacket

namespace AASCLinePacket

/-- An unbounded legal forward domain can remain empty for a whole history
while its unaltered transport rules remain jointly usable on every cell. -/
def vacuumLaw : Control := fun p _ =>
  (.pass, if p.2 = 0 then .right else .left)

def admitAt (x : ℕ) : Control := fun p m =>
  if p=(x,0) then (.pass,.left) else vacuumLaw p m

def tick (c : Control) : ℕ → State
  | 0 => initial
  | n+1 => advance c (tick c n)

theorem quiet_history (n : ℕ) : tick vacuumLaw n = some ((n,0),full) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tick,ih,advance,vacuumLaw,applyGate,next,full]

private theorem until_switch (x n : ℕ) (h : n≤x) :
    tick (admitAt x) n = some ((n,0),full) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have lt : n≠x := by omega
    simp [tick,ih (by omega),advance,admitAt,lt,vacuumLaw,applyGate,next,full]

theorem admitted_history (x k : ℕ) : tick (admitAt x) (x+k) = some ((x,k),full) := by
  induction k with
  | zero => simpa using until_switch x x le_rfl
  | succ k ih =>
    change advance (admitAt x) (tick (admitAt x) (x+k)) = _
    rw [ih]
    cases k <;> simp [advance,admitAt,vacuumLaw,applyGate,next,full]

/-- All sites in U have second null coordinate at least one. On a single
actual history the entire forward domain is quiet at all times. In a trial
that changes only the one boundary switch (x,0) outside U and agrees for
every earlier stage, the same original packet is observable at (x,y).
The controls inside U stay fixed for every x and y. -/
theorem operative_empty_cone (x y : ℕ) (hy : 0<y) :
    (∀ n a b : ℕ, 0<b → observe (a,b) (tick vacuumLaw n) = ∅) ∧
    agreeOff (x,0) (admitAt x) vacuumLaw ∧
    (∀ n, n≤x → tick (admitAt x) n = tick vacuumLaw n) ∧
    observe (x,y) (tick (admitAt x) (x+y)) = full ∧
    (x,0) ≠ (x,y) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro n a b hb
    simp [quiet_history,observe,Nat.ne_of_gt hb]
  · intro p outside m
    simp [admitAt,outside]
  · intro n hn
    rw [until_switch x n hn,quiet_history]
  · simp [admitted_history,observe]
  · simp [Nat.ne_of_lt hy]

end AASCLinePacket
