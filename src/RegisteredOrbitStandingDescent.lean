import AASC.Core.DeterminateObjecthood
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic

/-! The registered-witness part of W9 Definition10.1/Proposition10.2.
Inputs are RAW execution, comparison, phase and orbit-coequalizer data.
No orbit-state standing or desired original-source identification is a field.
Successful execution and the total execution ledger have different scopes. -/
noncomputable section
namespace AASCKleinGordon.W9

inductive RegisteredQuestion (Q : Type) where
  | execution (question : Q)
  | ledger (question : Q)

structure RawRegisteredOrbit (X Q V P : Type) where
  output : X → Q → V
  succeeds : V → Prop
  weight : X → X → ℝ
  outgoing : X → Q
  incoming : X → Q
  probabilityValue : ℝ → V
  probability_injective : Function.Injective probabilityValue
  outgoing_output : ∀ x z,output x (outgoing z)=probabilityValue (weight x z)
  incoming_output : ∀ x z,output x (incoming z)=probabilityValue (weight z x)
  probability_success : ∀ r,succeeds (probabilityValue r)
  orbit : X → X → Prop
  phase_output : ∀ x y,orbit x y → ∀ π,output x π=output y π
  raw_profiles_exact : ∀ x y,
    ((∀ z,weight x z=weight y z) ∧ (∀ z,weight z x=weight z y)) ↔ orbit x y
  q : X → P
  q_surjective : Function.Surjective q
  q_fibres : ∀ x y,q x=q y ↔ orbit x y
  coequalizer : ∀ {Y : Type} (f : X → Y),
    (∀ x y,orbit x y → f x=f y) → ∃! g : P → Y,∀ x,g (q x)=f x

namespace RawRegisteredOrbit
variable {X Q V P : Type} (D : RawRegisteredOrbit X Q V P)

def references : AASC.PartialReferenceSystem X (RegisteredQuestion Q) V := by
  classical
  exact ⟨fun x => fun
    | .execution π => if D.succeeds (D.output x π) then some (D.output x π) else none
    | .ledger π => some (D.output x π)⟩

def kernel : AASC.Kernel D.references.incidenceSystem := D.references.kernel

theorem reference_determinate : D.references.incidenceSystem.Determinate :=
  D.references.determinate

theorem kernel_reference_unique : D.kernel.ReferenceUnique :=
  D.kernel.reference_unique_of_determinate D.reference_determinate

theorem ledger_standing_iff (x : X) (π : Q) (v : V) :
    D.kernel.standing x (.ledger π) v ↔ D.output x π=v := by
  change some (D.output x π)=some v ↔ D.output x π=v
  constructor
  · exact Option.some.inj
  · exact congrArg some

theorem execution_standing_iff (x : X) (π : Q) (v : V) :
    D.kernel.standing x (.execution π) v ↔ D.succeeds (D.output x π) ∧ D.output x π=v := by
  classical
  change (if D.succeeds (D.output x π) then some (D.output x π) else none)=some v ↔ _
  by_cases h : D.succeeds (D.output x π) <;> simp [h]

theorem execution_failure_iff (x : X) (π : Q) :
    D.kernel.FailureAt x (.execution π) ↔ ¬ D.succeeds (D.output x π) := by
  classical
  change (∀ v,¬ D.references.incidenceSystem.incidence x (.execution π) v) ↔ _
  rw [← D.references.referenceAt_eq_none_iff]
  change (if D.succeeds (D.output x π) then some (D.output x π) else none)=none ↔ _
  by_cases h : D.succeeds (D.output x π) <;> simp [h]

theorem raw_probability_standing (x z : X) :
    D.kernel.standing x (.execution (D.outgoing z)) (D.probabilityValue (D.weight x z)) := by
  apply (D.execution_standing_iff _ _ _).mpr
  rw [D.outgoing_output]
  exact ⟨D.probability_success _,rfl⟩

def SameRegisteredStanding (x y : X) : Prop :=
  ∀ π v,D.kernel.standing x π v ↔ D.kernel.standing y π v

def SameRecord (x y : X) : Prop := ∀ π,D.output x π=D.output y π

theorem same_record_iff_registered (x y : X) :
    D.SameRecord x y ↔ D.SameRegisteredStanding x y := by
  constructor
  · intro same π v
    cases π with
    | execution π => rw [D.execution_standing_iff,D.execution_standing_iff,same π]
    | ledger π => rw [D.ledger_standing_iff,D.ledger_standing_iff,same π]
  · intro same π
    have hx : D.kernel.standing x (.ledger π) (D.output x π) :=
      (D.ledger_standing_iff _ _ _).mpr rfl
    exact ((D.ledger_standing_iff _ _ _).mp ((same _ _).mp hx)).symm

theorem same_record_iff_orbit (x y : X) : D.SameRecord x y ↔ D.orbit x y := by
  constructor
  · intro same
    apply (D.raw_profiles_exact x y).mp
    constructor
    · intro z
      apply D.probability_injective
      simpa only [D.outgoing_output] using same (D.outgoing z)
    · intro z
      apply D.probability_injective
      simpa only [D.incoming_output] using same (D.incoming z)
  · exact D.phase_output x y

/-- Neither finer nor coarser: all registered execution/report references,
including failure reports, identify exactly the already supplied raw orbit. -/
theorem registered_standing_exact (x y : X) :
    D.SameRegisteredStanding x y ↔ D.q x=D.q y :=
  (D.same_record_iff_registered x y).symm.trans
    ((D.same_record_iff_orbit x y).trans (D.q_fibres x y).symm)

def descend {Y : Type} (f : X → Y) (hf : ∀ x y,D.orbit x y → f x=f y) : P → Y :=
  (D.coequalizer f hf).choose

theorem descend_spec {Y : Type} (f : X → Y) (hf : ∀ x y,D.orbit x y → f x=f y) (x : X) :
    D.descend f hf (D.q x)=f x := (D.coequalizer f hf).choose_spec.1 x

theorem universal_standing_descent {Y : Type} (f : X → Y)
    (hf : ∀ x y,D.SameRegisteredStanding x y → f x=f y) :
    ∃! g : P → Y,∀ x,g (D.q x)=f x :=
  D.coequalizer f (fun x y h => hf x y ((D.registered_standing_exact x y).mpr
    ((D.q_fibres x y).mpr h)))

def standingRecord : P → Q → V :=
  D.descend D.output (fun x y h => funext (D.phase_output x y h))

theorem standing_record_spec (x : X) (π : Q) :
    D.standingRecord (D.q x) π=D.output x π :=
  congrFun (D.descend_spec D.output (fun x y h => funext (D.phase_output x y h)) x) π

theorem standing_record_injective : Function.Injective D.standingRecord := by
  intro r t h
  obtain ⟨x,rfl⟩ := D.q_surjective r
  obtain ⟨y,rfl⟩ := D.q_surjective t
  apply (D.q_fibres x y).mpr
  apply (D.same_record_iff_orbit x y).mp
  intro π
  have eq := congrFun h π
  simpa only [D.standing_record_spec] using eq

theorem standing_record_unique (R : P → Q → V)
    (hR : ∀ x π,R (D.q x) π=D.output x π) : R=D.standingRecord := by
  funext r π
  obtain ⟨x,rfl⟩ := D.q_surjective r
  exact (hR x π).trans (D.standing_record_spec x π).symm

theorem original_failure_retained (x : X) (π : Q) :
    ¬ D.succeeds (D.standingRecord (D.q x) π) ↔
      D.kernel.FailureAt x (.execution π) := by
  rw [D.standing_record_spec,D.execution_failure_iff]

theorem no_repair_of_the_same_failed_execution {x y : X} {π σ : Q}
    (success : D.succeeds (D.output x π)) (failure : ¬ D.succeeds (D.output y σ)) :
    ¬ Nonempty (D.references.incidenceSystem.Continuation
      (x,RegisteredQuestion.execution π) (y,RegisteredQuestion.execution σ)) := by
  apply D.kernel.noContinuation_of_standingToFailure
  refine ⟨⟨D.output x π,(D.execution_standing_iff _ _ _).mpr ⟨success,rfl⟩⟩,?_⟩
  exact (D.execution_failure_iff y σ).mpr failure

end RawRegisteredOrbit
end AASCKleinGordon.W9
