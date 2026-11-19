import OrderObstruction

/-! Independently written finite sets of record identifiers on a two-direction
grid. At each site one register merges local writes with accepted records
from its southern neighbour. A second register merges that result with
accepted records from its western neighbour. The checkpoint is this second
register. Each mask acts on an incoming port; an all-clear control is legal.
An optional local display can request a subset of an occupied checkpoint. -/
namespace AASCMultiRecordRelay

abbrev Site := Nat × Nat
abbrev Writes (L : Type*) := Site → Finset L

structure Controls (L : Type*) where
  fromSouth : Site → L → Bool
  fromWest : Site → L → Bool

def clear {L : Type*} : Controls L := ⟨fun _ _ => true, fun _ _ => true⟩

variable {L : Type*} [DecidableEq L]

/-- At a successor, the only inputs are the local insertion and the one
incoming register. -/
def scan (fresh : Nat → Finset L) (accept : Nat → L → Bool) : Nat → Finset L
  | 0 => fresh 0
  | n+1 => (scan fresh accept n).filter (fun tag => accept (n+1) tag) ∪ fresh (n+1)

def northRegister (w : Writes L) (c : Controls L) (x y : Nat) : Finset L :=
  scan (fun b => w (x,b)) (fun b => c.fromSouth (x,b)) y

def checkpoint (w : Writes L) (c : Controls L) (p : Site) : Finset L :=
  scan (fun a => northRegister w c a p.2) (fun a => c.fromWest (a,p.2)) p.1

def display (stored requested : Finset L) : Finset L := stored ∩ requested

theorem two_marker_query (stored : Finset L) (i j : L) :
    i ∈ display stored {i,j} ∧ j ∈ display stored {i,j} ↔ i ∈ stored ∧ j ∈ stored := by
  simp [display]

private theorem scan_local (a b : Nat → Finset L) (accept : Nat → L → Bool) (n : Nat)
    (same : ∀ k ≤ n, a k = b k) : scan a accept n = scan b accept n := by
  induction n with
  | zero => exact same _ (by omega)
  | succ n ih => rw [scan,scan,ih (fun k hk => same k (by omega)),same _ (by omega)]

theorem checkpoint_locality (w v : Writes L) (c : Controls L) (q : Site)
    (same : ∀ s ≤ q, w s = v s) : checkpoint w c q = checkpoint v c q := by
  apply scan_local
  intro x hx
  apply scan_local
  exact fun y hy => same (x,y) ⟨hx,hy⟩

private theorem mem_clear_scan (a : Nat → Finset L) (n : Nat) (tag : L) :
    tag ∈ scan a (fun _ _ => true) n ↔ ∃ k ≤ n, tag ∈ a k := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    simp only [scan,Finset.mem_union,Finset.mem_filter,and_true,ih]
    constructor
    · rintro (⟨k,hk,mem⟩ | mem)
      · exact ⟨k,by omega,mem⟩
      · exact ⟨n+1,le_rfl,mem⟩
    · rintro ⟨k,hk,mem⟩
      by_cases h : k = n+1
      · exact Or.inr (h ▸ mem)
      · exact Or.inl ⟨k,by omega,mem⟩

theorem clear_checkpoint_reads (w : Writes L) (q : Site) (tag : L) :
    tag ∈ checkpoint w clear q ↔ ∃ s ≤ q, tag ∈ w s := by
  change tag ∈ scan _ (fun _ _ => true) _ ↔ _
  rw [mem_clear_scan]
  constructor
  · rintro ⟨x,hx,token⟩
    obtain ⟨y,hy,mem⟩ := (mem_clear_scan _ _ _).mp token
    exact ⟨(x,y),⟨hx,hy⟩,mem⟩
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,mem⟩
    exact ⟨x,hx,(mem_clear_scan _ _ _).mpr ⟨y,hy,mem⟩⟩

theorem retained_at_future_clear_checkpoint (w : Writes L) (p q : Site) (future : p ≤ q) :
    checkpoint w clear p ⊆ checkpoint w clear q := by
  intro tag present
  obtain ⟨s,h,mem⟩ := (clear_checkpoint_reads _ _ _).mp present
  exact (clear_checkpoint_reads _ _ _).mpr ⟨s,h.trans future,mem⟩

def insertAt (w : Writes L) (source : Site) (tag : L) : Writes L :=
  fun p => if p = source then insert tag (w p) else w p

/-- Both experiments use the same background writes and port controls.
Only the chosen record at the chosen original source can differ. -/
def CanSignal (source detector : Site) (tag : L) : Prop :=
  ∃ (w : Writes L) (c : Controls L),
    tag ∈ checkpoint (insertAt w source tag) c detector ∧ tag ∉ checkpoint w c detector

theorem signal_iff_product_order (source detector : Site) (tag : L) :
    CanSignal source detector tag ↔ source ≤ detector := by
  constructor
  · rintro ⟨w,c,on,off⟩
    by_contra outside
    have same := checkpoint_locality (insertAt w source tag) w c detector
      (fun s hs => by
        have ne : s ≠ source := by rintro rfl; exact outside hs
        simp [insertAt,ne])
    exact off (same ▸ on)
  · intro inside
    refine ⟨fun _ => ∅,clear,(clear_checkpoint_reads _ _ _).mpr ?_,?_⟩
    · exact ⟨source,inside,by simp [insertAt]⟩
    · simp [clear_checkpoint_reads]

/-- The original source at each site writes all enabled slots allocated
to that site. Every subset of an arbitrary finite family is a legal input. -/
def writeSlots {n : Nat} (whereAt : Fin n → Site) (enabled : Finset (Fin n)) :
    Writes (Fin n) := fun p => enabled.filter (fun i => whereAt i = p)

theorem clear_slot_readout {n : Nat} (whereAt : Fin n → Site) (enabled : Finset (Fin n))
    (q : Site) (i : Fin n) :
    i ∈ checkpoint (writeSlots whereAt enabled) clear q ↔ i ∈ enabled ∧ whereAt i ≤ q := by
  rw [clear_checkpoint_reads]
  constructor
  · rintro ⟨p,h,mem⟩
    obtain ⟨on,location⟩ := Finset.mem_filter.mp mem
    exact ⟨on,location ▸ h⟩
  · rintro ⟨on,h⟩
    exact ⟨whereAt i,h,Finset.mem_filter.mpr ⟨on,rfl⟩⟩

/-- Switching a single original marker while arbitrary other markers remain
on has exactly the product-order effect under one fixed transparent control. -/
theorem switch_one_in_common_background {n : Nat} (whereAt : Fin n → Site)
    (enabled : Finset (Fin n)) (q : Site) (i : Fin n) (off : i ∉ enabled) :
    (i ∈ checkpoint (writeSlots whereAt (insert i enabled)) clear q ∧
     i ∉ checkpoint (writeSlots whereAt enabled) clear q) ↔ whereAt i ≤ q := by
  simp [clear_slot_readout,off]

theorem independent_slots_at_one_checkpoint {n : Nat} (whereAt : Fin n → Site)
    (enabled : Finset (Fin n)) (q : Site) (arrive : ∀ i, whereAt i ≤ q) :
    checkpoint (writeSlots whereAt enabled) clear q = enabled := by
  ext i
  rw [clear_checkpoint_reads]
  constructor
  · rintro ⟨p,_,mem⟩
    exact (Finset.mem_filter.mp mem).1
  · intro active
    exact ⟨whereAt i,arrive i,Finset.mem_filter.mpr ⟨active,rfl⟩⟩

def earlySite (i : Fin 3) : Site := (i.val,2-i.val)
def lateSite (i : Fin 3) : Site := (2+i.val,4-i.val)

theorem three_distinct_sources : Function.Injective earlySite := by
  intro i j same
  exact Fin.ext (congrArg Prod.fst same)

theorem original_sources_incomparable (i j : Fin 3) : earlySite i ≤ earlySite j ↔ i = j := by
  have hi := i.isLt
  have hj := j.isLt
  constructor
  · rintro ⟨hfront,hback⟩
    dsimp [earlySite] at hfront hback
    apply Fin.ext
    omega
  · rintro rfl
    exact le_rfl

theorem three_independent_at_join (enabled : Finset (Fin 3)) :
    checkpoint (writeSlots earlySite enabled) clear (2,2) = enabled := by
  apply independent_slots_at_one_checkpoint
  intro i
  exact ⟨by have := i.isLt; dsimp [earlySite]; omega, by simp [earlySite]⟩

private theorem all_early_to_all_late (i j : Fin 3) : earlySite i ≤ lateSite j := by
  have hi := i.isLt
  have hj := j.isLt
  constructor <;> dsimp [earlySite,lateSite] <;> omega

/-- Local requests can show exactly the off-diagonal labels, using one
fixed panel at each late site; each geometric source can still influence
each late site. The display predicate is a different original observable. -/
def requestedAt (q : Site) : Finset (Fin 3) := Finset.univ.filter (fun i => q ≠ lateSite i)

theorem masked_reports_and_full_influence (i j : Fin 3) :
    (i ∈ display (checkpoint (writeSlots earlySite Finset.univ) clear (lateSite j))
      (requestedAt (lateSite j)) ↔ i ≠ j) ∧ CanSignal (earlySite i) (lateSite j) i := by
  have inj : Function.Injective lateSite := by
    intro k l h
    have hval := congrArg Prod.fst h
    apply Fin.ext
    dsimp [lateSite] at hval
    omega
  rw [independent_slots_at_one_checkpoint _ _ _ (fun k => all_early_to_all_late k j)]
  refine ⟨?_,(signal_iff_product_order _ _ _).mpr (all_early_to_all_late i j)⟩
  simp [display,requestedAt,inj.eq_iff,ne_comm]

/-- No selection of six original sites has the off-diagonal-only pattern
for actual signal access, even with independently programmable port masks. -/
theorem no_six_sites {n : Nat} (tags : Fin 3 → Fin n) (a b : Fin 3 → Site) :
    ¬ ∀ i j, CanSignal (a i) (b j) (tags i) ↔ i ≠ j := by
  intro pattern
  apply AASCOrderObstruction.two_orders_exclude_three_diagonals a b
  exact fun i j => (signal_iff_product_order _ _ _).symm.trans (pattern i j)

end AASCMultiRecordRelay
