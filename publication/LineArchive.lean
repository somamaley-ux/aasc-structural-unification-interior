import LocalAuditCone
import LineFieldBridge
import LineOrder

/-! Local audit memory coupled to the actual single-origin packet controller.

An event is one cell update with local mask observation and local applied gate.
The archive is an additional local carrier. It cannot change the particle state. -/
namespace AASCLineArchive

open AASCLinePacket AASCLineFieldBridge
set_option autoImplicit false

deriving instance DecidableEq for AASCLinePacket.Gate

/-- A site-indexed control may depend on the actual input mask. A native packet
visits each site at most once, at the rank fixed by its null coordinates. -/
def slice (w : Control) : ℕ → State
  | 0 => initial
  | n+1 => advance w (slice w n)

private theorem slice_replicate (w : Control) (n : ℕ) :
    slice w n = run (List.replicate n w) initial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [slice, ih, List.replicate_succ']
    simp [run,List.foldl_append]

/-- The original control program may choose a different site controller on
each successive tick. -/
def scheduled (c : ℕ → Control) : ℕ → State
  | 0 => initial
  | n+1 => advance (c n) (scheduled c n)

def programAtRank (c : ℕ → Control) : Control := fun p => c (rank p) p

/-- Restricting a timed program to the physically occupied time at each cell
preserves *every* packet slice, including extinction and all damage masks. -/
theorem all_timed_programs_realized (c : ℕ → Control) (n : ℕ) :
    slice (programAtRank c) n = scheduled c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [slice, scheduled, ← ih]
    cases h : slice (programAtRank c) n with
    | none => rfl
    | some occupied =>
      obtain ⟨p,m⟩ := occupied
      rw [slice_replicate] at h
      have timing := native_stage_count (List.replicate n (programAtRank c)) (0,0) p full m h
      have tick : rank p = n := by simpa [rank] using timing
      simp [advance,programAtRank,tick]

private theorem pred_le {p q : Site} (h : Incoming p q) : p ≤ q := by
  obtain ⟨u,v⟩ := p
  rcases h with h | h <;> subst q <;> constructor <;> simp [next]

theorem slice_observation_from_past (w v : Control) (n : ℕ) (q : Site)
    (same : ∀ k ≤ q, w k = v k) : observe q (slice w n) = observe q (slice v n) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    ext i
    rw [slice, slice, field_step_exact, field_step_exact]
    apply field_update_local
    intro p predecessor
    have leq := pred_le predecessor
    have mask := ih p (fun k hk => same k (hk.trans leq))
    exact ⟨mask,by rw [mask,same p leq]⟩

def nativeMask (w : Control) (p : Site) := observe p (slice w (p.1+p.2))
abbrev Act := Mask × Gate × Dir

/-- An applied act is the observed mask and the gate and direction actually
selected on that input. Unused branches of the controller are never logged. -/
def appliedAct (w : Control) (p : Site) : Act :=
  let m := nativeMask w p
  (m,w p m)

private theorem act_from_past (w v : Control) (q : Site) (same : ∀ k ≤ q, w k = v k) :
    appliedAct w q = appliedAct v q := by
  have hm : nativeMask w q = nativeMask v q := slice_observation_from_past w v _ q same
  simp only [appliedAct,hm,same q le_rfl]

private def tape : AASCLocalAudit.Rule Act Mask := fun _ a _ _ => a.1
def instrumented (w : Control) (q : Site) : AASCLocalAudit.WithLog Act Mask :=
  AASCLocalAudit.reading ((∅ : Mask),∅) (AASCLocalAudit.archiveRule tape) (appliedAct w) q

private theorem tape_reading (w : Control) (p : Site) :
    AASCLocalAudit.reading (∅ : Mask) tape (appliedAct w) p = nativeMask w p := by
  unfold AASCLocalAudit.reading
  rw [AASCLocalAudit.run]
  rfl

/-- For every native control and cell the packet reading is exactly the one
computed with the original launch, mask damage, majority repair and routing. -/
theorem native_mask_preserved (w : Control) (q : Site) :
    (instrumented w q).1 = nativeMask w q := by
  rw [instrumented,AASCLocalAudit.archive_projects,tape_reading]

theorem native_entry_recovered (w : Control) (p q : Site) (a : Act) (m : Mask) :
    (p,a,m) ∈ (instrumented w q).2 ↔ p ≤ q ∧ a = appliedAct w p ∧ m = nativeMask w p := by
  rw [instrumented,AASCLocalAudit.original_entry_in_archive,tape_reading]

theorem native_history_recoverable_at (w : Control) {p q : Site} (h : p ≤ q) :
    (instrumented w p).2 = (instrumented w q).2.filter (fun e => e.1 ≤ p) :=
  AASCLocalAudit.earlier_archive_from_later _ _ _ h

def CanSignal (p q : Site) : Prop :=
  ∃ w v : Control, (∀ k ≠ p, w k = v k) ∧ instrumented w q ≠ instrumented v q

theorem instrumented_access (p q : Site) : CanSignal p q ↔ p ≤ q := by
  constructor
  · rintro ⟨w,v,elsewhere,change⟩
    by_contra outside
    apply change
    apply AASCLocalAudit.past_determines_reading
    intro k hk
    exact act_from_past _ _ _ (fun s hs =>
      elsewhere s (fun eq => outside (eq ▸ hs.trans hk)))
  · intro future
    let w : Control := drift .right
    let v : Control := fun k => if k = p then (drift .left k) else w k
    refine ⟨w,v,fun k ne => by simp [v,ne],?_⟩
    have entry := (native_entry_recovered w p q _ _).mpr ⟨future,rfl,rfl⟩
    intro eq
    rw [eq] at entry
    have actual := ((native_entry_recovered ..).mp entry).2.1
    have direction := congrArg (fun a : Act => a.2.2) actual
    simp [appliedAct,w,v,drift] at direction

/-- The original single-packet intervention order and the local ledger's full
single-control influence order coincide on the same physically indexed cells. -/
theorem instrumentation_preserves_native_access (p q : Site) :
    CanSignal p q ↔ CompleteAccess p q :=
  (instrumented_access p q).trans (complete_access_exact p q).symm

theorem no_six_with_native_histories (a b : Fin 3 → Site) :
    ¬ ∀ i j, CanSignal (a i) (b j) ↔ i ≠ j := by
  intro pattern
  apply AASCOrderObstruction.two_orders_exclude_three_diagonals a b
  intro i j
  exact (instrumented_access _ _).symm.trans (pattern i j)

end AASCLineArchive
