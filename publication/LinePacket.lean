import OrderObstruction

/-! A single-origin, locally steered packet on the future checkerboard of a
one-dimensional nearest-neighbour lattice. All timelike histories and all
observations below use the same carrier. -/

namespace AASCLinePacket

abbrev Site := ℕ × ℕ
abbrev Lane := Fin 3
abbrev Mask := Finset Lane
abbrev State := Option (Site × Mask)

inductive Dir | right | left deriving DecidableEq
inductive Gate | pass | damage (survive : Mask) | repair
def full : Mask := Finset.univ
def applyGate : Gate → Mask → Mask
  | .pass, m => m
  | .damage s, m => m ∩ s
  | .repair, m => if 2 ≤ m.card then full else ∅

def next : Dir → Site → Site
  | .right, (u,v) => (u+1,v)
  | .left, (u,v) => (u,v+1)

/-- A controller can depend on both its own site and its incoming lane record. -/
abbrev Control := Site → Mask → Gate × Dir
def advance (c : Control) : State → State
  | none => none
  | some (p,m) =>
    let a := c p m
    let s := applyGate a.1 m
    if s.Nonempty then some (next a.2 p,s) else none
def run (cs : List Control) (s : State) : State := cs.foldl (fun v c => advance c v) s
def observe (p : Site) : State → Mask
  | none => ∅
  | some (q,m) => if p=q then m else ∅

def put (p : Site) (m : Mask) : State := if m.Nonempty then some (p,m) else none
def initial : State := some ((0,0),full)
def drift (d : Dir) : Control := fun _ _ => (.pass,d)
def moves (u v : ℕ) : List Control :=
  List.replicate u (drift .right) ++ List.replicate v (drift .left)

private theorem full_nonempty : full.Nonempty := ⟨0, Finset.mem_univ _⟩

theorem no_recreation (cs : List Control) : run cs none = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

private theorem advance_drift (d : Dir) (p : Site) :
    advance (drift d) (some (p,full)) = some (next d p,full) := by
  simp [advance,drift,applyGate,full_nonempty]

private theorem right_steps (k : ℕ) (p : Site) :
    run (List.replicate k (drift .right)) (some (p,full)) = some ((p.1+k,p.2),full) := by
  induction k generalizing p with
  | zero => simp [run]
  | succ k ih =>
    rw [List.replicate_succ]
    change run _ (advance _ _) = _
    rw [advance_drift,ih]
    cases p; simp [next]; omega

private theorem left_steps (k : ℕ) (p : Site) :
    run (List.replicate k (drift .left)) (some (p,full)) = some ((p.1,p.2+k),full) := by
  induction k generalizing p with
  | zero => simp [run]
  | succ k ih =>
    rw [List.replicate_succ]
    change run _ (advance _ _) = _
    rw [advance_drift,ih]
    cases p; simp [next]; omega

theorem steering (p : Site) (u v : ℕ) :
    run (moves u v) (some (p,full)) = some ((p.1+u,p.2+v),full) := by
  unfold moves
  change List.foldl _ _ _ = _
  rw [List.foldl_append]
  change run _ (run _ _) = _
  rw [right_steps,left_steps]

private theorem next_above (p : Site) (d : Dir) : p ≤ next d p := by
  cases p; cases d <;> exact ⟨by simp[next],by simp[next]⟩

private def InFuture (p : Site) : State → Prop
  | none => True
  | some (q,_) => p ≤ q

private theorem run_future (p : Site) (cs : List Control) (s : State) (h : InFuture p s) :
    InFuture p (run cs s) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih =>
    apply ih
    cases s with
    | none => trivial
    | some v =>
      rcases v with ⟨q,m⟩
      unfold advance
      dsimp only
      split
      · exact le_trans h (next_above q _)
      · trivial

private theorem read_empty_outside {p q : Site} {s : State} (h : InFuture p s) (outside : ¬p≤q) :
    observe q s = ∅ := by
  cases s with
  | none => rfl
  | some v =>
    rcases v with ⟨r,m⟩
    have hqr : q ≠ r := by intro eq; subst r; exact outside h
    simp [observe,hqr]

/-- Start with the unique original launch. Two choices of local damage at a
visited event, compared under the same subsequent controls. A reading is
the remaining physical lane pattern at the named site. -/
def CanAffect (p q : Site) : Prop :=
  ∃ (pre post : List Control) (m a b : Mask),
    run pre initial = some (p,m) ∧
    observe q (run post (put p (m ∩ a))) ≠ observe q (run post (put p (m ∩ b)))

theorem causal_access (p q : Site) : CanAffect p q ↔ p ≤ q := by
  constructor
  · rintro ⟨pre,post,m,a,b,_,neq⟩
    by_contra outside
    have empty (s : Mask) : observe q (run post (put p s)) = ∅ := by
      apply read_empty_outside (p:=p) _ outside
      apply run_future
      unfold put
      split
      · exact le_rfl
      · trivial
    exact neq ((empty _).trans (empty _).symm)
  · intro h
    have hp : run (moves p.1 p.2) initial = some (p,full) := by
      unfold initial
      rw [steering]
      simp
    have hq : run (moves (q.1-p.1) (q.2-p.2)) (some (p,full)) = some (q,full) := by
      rw [steering,Nat.add_sub_of_le h.1,Nat.add_sub_of_le h.2]
    exact ⟨moves p.1 p.2,moves (q.1-p.1) (q.2-p.2),full,full,∅,hp,by
      simp only [Finset.inter_self,Finset.inter_empty,put,if_pos full_nonempty,
        Finset.not_nonempty_empty,if_false,hq,no_recreation]
      simpa [observe] using full_nonempty.ne_empty⟩

theorem no_six_events (a b : Fin 3 → Site) :
    ¬ ∀ i j, CanAffect (a i) (b j) ↔ i ≠ j := by
  intro h
  exact AASCOrderObstruction.two_orders_exclude_three_diagonals a b
    (fun i j => (causal_access (a i) (b j)).symm.trans (h i j))

theorem single_site_per_slice (cs : List Control) (p q : Site)
    (hp : (observe p (run cs initial)).Nonempty) (hq : (observe q (run cs initial)).Nonempty) : p=q := by
  cases s : run cs initial with
  | none => simp [s,observe] at hp
  | some v =>
    rcases v with ⟨r,m⟩
    rw [s] at hp hq
    by_contra ne
    by_cases pr : p = r
    · have qr : q ≠ r := fun h => ne (pr.trans h.symm)
      simp [observe,qr] at hq
    · simp [observe,pr] at hp

def maskedStep (m : Mask) (d : Dir) : Control := fun _ _ => (.damage m,d)
def repairStep (d : Dir) : Control := fun _ _ => (.repair,d)

/-- Two distinct ticks expose damage and repair. Subsequent response to every
control sequence agrees with that of the intact transported original precisely
on the repairable side of the threshold. -/
theorem same_origin_repair (p : Site) (m : Mask) (a b : Dir) :
    run [maskedStep m a, repairStep b] (some (p,full)) =
      if 2 ≤ m.card then some (next b (next a p),full) else none := by
  by_cases hm : m.Nonempty
  · by_cases hc : 2 ≤ m.card <;>
      simp [run,advance,maskedStep,repairStep,applyGate,full,hm,hc]
  · have emp : m=∅ := Finset.not_nonempty_iff_eq_empty.mp hm
    simp [emp,run,advance,maskedStep,applyGate,full]

theorem all_future_after_repair (p : Site) (m : Mask) (a b : Dir)
    (hc : 2 ≤ m.card) (future : List Control) :
    run future (run [maskedStep m a, repairStep b] (some (p,full))) =
    run future (some (next b (next a p),full)) := by
  rw [same_origin_repair,if_pos hc]

/-- A no-particle stage with the same available carrier can receive an
incoming boundary packet in a different preparation. The empty-history
counterfactual cannot re-create that packet under the same continuation. -/
theorem vacuum_transfer (p : Site) (u v : ℕ) :
    run (moves u v) none = none ∧
    run (moves u v) (some (p,full)) = some ((p.1+u,p.2+v),full) :=
  ⟨no_recreation _,steering _ _ _⟩

def agreeOff (p : Site) (c d : Control) : Prop :=
  ∀ q, q ≠ p → ∀ m, c q m = d q m

private def agreeOrFuture (p : Site) (s z : State) : Prop :=
  s=z ∨ InFuture p s ∧ InFuture p z

private theorem step_future (p : Site) (c : Control) (s : State) (h : InFuture p s) :
    InFuture p (advance c s) := run_future p [c] s h

private theorem step_compare {p : Site} {s z : State} {c d : Control}
    (eq : agreeOff p c d) (h : agreeOrFuture p s z) :
    agreeOrFuture p (advance c s) (advance d z) := by
  rcases h with same | ⟨hs,hz⟩
  · subst z
    cases s with
    | none => exact Or.inl rfl
    | some v =>
      rcases v with ⟨q,m⟩
      by_cases qp : q=p
      · subst q
        exact Or.inr ⟨step_future p c _ (show p≤p from le_rfl),
                      step_future p d _ (show p≤p from le_rfl)⟩
      · exact Or.inl (by simp only [advance,eq q qp m])
  · exact Or.inr ⟨step_future p c _ hs,step_future p d _ hz⟩

private theorem compare_runs {p : Site} {cs ds : List Control} {s z : State}
    (changes : List.Forall₂ (agreeOff p) cs ds) (h : agreeOrFuture p s z) :
    agreeOrFuture p (run cs s) (run ds z) := by
  induction changes generalizing s z with
  | nil => exact h
  | cons head _ ih => exact ih (step_compare head h)

/-- In addition to immediate lane interventions, the full family compares
arbitrary site- and state-dependent gate and routing programs. They may
differ at the source, and agree at every other site on every input. -/
def CompleteAccess (p q : Site) : Prop :=
  CanAffect p q ∨ ∃ cs ds : List Control, List.Forall₂ (agreeOff p) cs ds ∧
    observe q (run cs initial) ≠ observe q (run ds initial)

theorem complete_access_exact (p q : Site) : CompleteAccess p q ↔ p≤q := by
  constructor
  · rintro (h | ⟨cs,ds,changes,ne⟩)
    · exact (causal_access p q).mp h
    · by_contra outside
      rcases compare_runs changes (show agreeOrFuture p initial initial from Or.inl rfl) with
        same | ⟨hs,hz⟩
      · exact ne (congrArg (observe q) same)
      · exact ne ((read_empty_outside hs outside).trans (read_empty_outside hz outside).symm)
  · exact fun h => Or.inl ((causal_access p q).mpr h)

theorem no_six_complete_access (a b : Fin 3 → Site) :
    ¬ ∀ i j, CompleteAccess (a i) (b j) ↔ i ≠ j := by
  intro h
  exact AASCOrderObstruction.two_orders_exclude_three_diagonals a b
    (fun i j => (complete_access_exact (a i) (b j)).symm.trans (h i j))

end AASCLinePacket
