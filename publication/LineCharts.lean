import LinePacket

namespace AASCLinePacket

abbrev Charts := Site → Equiv.Perm Lane
def rename (e : Equiv.Perm Lane) (m : Mask) := m.map e.toEmbedding
def inChart (g : Charts) : State → State
  | none => none
  | some (p,m) => some (p,rename (g p) m)

private theorem rename_undo (e : Equiv.Perm Lane) (m : Mask) :
    rename e.symm (rename e m) = m := by
  ext i
  simp [rename]

theorem chart_roundtrip (g : Charts) (s : State) :
    inChart (fun p => (g p).symm) (inChart g s) = s := by
  cases s with
  | none => rfl
  | some v => rcases v with ⟨p,m⟩; simp only [inChart,rename_undo]

def gateIn (e : Equiv.Perm Lane) : Gate → Gate
  | .pass => .pass
  | .damage m => .damage (rename e m)
  | .repair => .repair

theorem gate_equivariant (e : Equiv.Perm Lane) (g : Gate) (m : Mask) :
    applyGate (gateIn e g) (rename e m) = rename e (applyGate g m) := by
  cases g with
  | pass => rfl
  | damage s => simp [gateIn,applyGate,rename,Finset.map_inter]
  | repair =>
    by_cases h : 2 ≤ m.card <;> simp [gateIn,applyGate,rename,h,full]

/-- A link changes chart from source to destination. The controller consumes a
local word, applies the reindexed local mask or repair, then transports the
result with the link transition. Source and destination charts may be chosen
independently. -/
def chartAdvance (g : Charts) (c : Control) : State → State
  | none => none
  | some (p,m) =>
    let a := c p (rename (g p).symm m)
    let w := applyGate (gateIn (g p) a.1) m
    let q := next a.2 p
    if w.Nonempty then some (q,rename (g q) (rename (g p).symm w)) else none

theorem local_chart_commutes (g : Charts) (c : Control) (s : State) :
    chartAdvance g c (inChart g s) = inChart g (advance c s) := by
  cases s with
  | none => rfl
  | some v =>
    rcases v with ⟨p,m⟩
    simp only [inChart,chartAdvance,rename_undo,gate_equivariant,advance]
    by_cases h : (applyGate (c p m).1 m).Nonempty
    · have h' : (rename (g p) (applyGate (c p m).1 m)).Nonempty := by
        simpa [rename] using h
      simp only [if_pos h,if_pos h']
    · have h' : ¬(rename (g p) (applyGate (c p m).1 m)).Nonempty := by
        simpa [rename] using h
      simp only [if_neg h,if_neg h']

theorem all_chart_runs_commute (g : Charts) (cs : List Control) (s : State) :
    cs.foldl (fun z c => chartAdvance g c z) (inChart g s) = inChart g (run cs s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [local_chart_commutes,ih]
    rfl

end AASCLinePacket
