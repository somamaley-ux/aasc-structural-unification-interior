import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

/-! A one-tick original experiment on a directed ring. A detector samples
its local input and the preceding station. A source signals to a detector
when two admitted preparations differ only at the source and give different
detector answers. No distance or prior comparison table is used. -/
namespace AASCLocalExperiment

open Set
set_option autoImplicit false

variable {I X Y : Type*}

def CanSignal (S : Set (I → X)) (observe : (I → X) → I → Y) (i k : I) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, (∀ j, j ≠ i → a j = b j) ∧ observe a k ≠ observe b k

def gateReading (prev : I → I) (gate : I → X → X → Y) (a : I → X) (k : I) : Y :=
  gate k (a k) (a (prev k))

def ownInputDetectable (g : X → X → Y) : Prop :=
  ∃ a b c, g a c ≠ g b c

def incomingInputDetectable (g : X → X → Y) : Prop :=
  ∃ a b c, g a b ≠ g a c

def pulse [DecidableEq I] (source : I) (on off : X) (j : I) : X :=
  if j = source then on else off

/-- The upper bound holds for any set of allowed source preparations. -/
theorem signal_must_use_a_gate_input (S : Set (I → X)) (prev : I → I)
    (gate : I → X → X → Y) (i k : I)
    (path : CanSignal S (gateReading prev gate) i k) : i = k ∨ i = prev k := by
  classical
  obtain ⟨a,_,b,_,off,detected⟩ := path
  by_cases localInput : i = k
  · exact Or.inl localInput
  · right
    by_contra incoming
    exact detected (congrArg₂ (gate k) (off k (Ne.symm localInput))
      (off (prev k) (Ne.symm incoming)))

/-- With free source settings, the accessible inputs are exactly the
individually detectable arguments of the gate. The other argument is held fixed. -/
theorem unrestricted_signal_iff_detectable_input (prev : I → I)
    (gate : I → X → X → Y) (i k : I) (different : k ≠ prev k) :
    CanSignal univ (gateReading prev gate) i k ↔
      (i = k ∧ ownInputDetectable (gate k)) ∨
      (i = prev k ∧ incomingInputDetectable (gate k)) := by
  classical
  constructor
  · intro signal
    have inputs := signal_must_use_a_gate_input _ prev gate i k signal
    obtain ⟨a,_,b,_,off,observed⟩ := signal
    change gate k (a k) (a (prev k)) ≠ gate k (b k) (b (prev k)) at observed
    rcases inputs with self | incoming
    · subst i
      left
      rw [← off _ different.symm] at observed
      exact ⟨rfl,a k,b k,a (prev k),observed⟩
    · subst i
      right
      rw [← off _ different] at observed
      exact ⟨rfl,a k,a (prev k),b (prev k),observed⟩
  · rintro (⟨self,a,b,c,h⟩ | ⟨incoming,a,b,c,h⟩)
    · subst i
      refine ⟨pulse k a c,mem_univ _,pulse k b c,mem_univ _,?_,?_⟩
      · intro j hj
        simp [pulse,hj]
      · simpa [gateReading,pulse,different.symm] using h
    · subst i
      refine ⟨pulse (prev k) b a,mem_univ _,pulse (prev k) c a,mem_univ _,?_,?_⟩
      · intro j hj
        simp [pulse,hj]
      · simpa [gateReading,pulse,different] using h

def predecessor (k : Fin 3) : Fin 3 := k+2
def lateStation (j : Fin 3) : Fin 3 := j+2

private theorem station_distinct (k : Fin 3) : k ≠ predecessor k :=
  (by decide : ∀ k : Fin 3, k ≠ predecessor k) k

private theorem ring_inputs (i j : Fin 3) :
    i = lateStation j ∨ i = predecessor (lateStation j) ↔ i ≠ j :=
  (by decide : ∀ i j : Fin 3, i = lateStation j ∨ i = predecessor (lateStation j) ↔ i ≠ j) i j

/-- The six-event comparison occurs precisely when both input channels of
every station can be detected, possibly using different original settings. -/
theorem ring_pattern_iff_detectable_gates (gate : Fin 3 → X → X → Y) :
    (∀ i j, CanSignal univ (gateReading predecessor gate) i (lateStation j) ↔ i ≠ j) ↔
      ∀ k, ownInputDetectable (gate k) ∧ incomingInputDetectable (gate k) := by
  constructor
  · intro pattern k
    obtain ⟨j,hj⟩ := (by decide : ∀ k : Fin 3, ∃ j : Fin 3, lateStation j = k) k
    have channel (i : Fin 3) (input : i = k ∨ i = predecessor k) :=
      (unrestricted_signal_iff_detectable_input predecessor gate i k (station_distinct k)).mp
        (by rw [← hj] at input ⊢; exact (pattern i j).mpr ((ring_inputs i j).mp input))
    constructor
    · rcases channel k (.inl rfl) with h | h
      · exact h.2
      · exact (station_distinct k h.1).elim
    · rcases channel (predecessor k) (.inr rfl) with h | h
      · exact (station_distinct k h.1.symm).elim
      · exact h.2
  · intro active i j
    rw [unrestricted_signal_iff_detectable_input predecessor gate i _ (station_distinct _)]
    simp only [(active _).1,(active _).2,and_true]
    exact ring_inputs i j

/-- Only four source assignments are required for a common one-pulse test:
the quiet assignment and one isolated pulse at each of the three stations.
The locality upper bound still covers every admitted intervention. -/
theorem four_preparations_supply_six_events (S : Set (Fin 3 → X))
    (gate : Fin 3 → X → X → Y) (on off : X)
    (quiet : (fun _ => off) ∈ S) (pulses : ∀ i, pulse i on off ∈ S)
    (own : ∀ k, gate k on off ≠ gate k off off)
    (incoming : ∀ k, gate k off on ≠ gate k off off) :
    ∀ i j, CanSignal S (gateReading predecessor gate) i (lateStation j) ↔ i ≠ j := by
  intro i j
  constructor
  · intro signal
    exact (ring_inputs i j).mp (signal_must_use_a_gate_input _ _ _ _ _ signal)
  · intro distinct
    refine ⟨pulse i on off,pulses i,fun _ => off,quiet,?_,?_⟩
    · intro k hk
      simp [pulse,hk]
    · rcases (ring_inputs i j).mpr distinct with rfl | rfl
      · simpa [gateReading,pulse,(station_distinct _).symm] using own (lateStation j)
      · simpa [gateReading,pulse,station_distinct] using incoming (lateStation j)

theorem boolean_or_ring_experiment (i j : Fin 3) :
    CanSignal univ (gateReading predecessor fun _ (a b : Bool) => a || b) i (lateStation j) ↔ i ≠ j :=
  four_preparations_supply_six_events univ (fun _ a b => a || b) true false (mem_univ _)
    (fun _ => mem_univ _) (fun _ => Bool.noConfusion) (fun _ => Bool.noConfusion) i j

end AASCLocalExperiment
