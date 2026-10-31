import KernelReference.ObjecthoodNecessity
import KernelReference.DependentConservation
import KernelReference.EqualityPatterns
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic

/-! The AMetric restrictions actually used by Metricity 4.6/6.2/7.2.
Original incidence, retained maps, eligible families and grounded rules are raw
inputs. No license, agreement, minimal interface or output-soundness field is
assumed. This is not a formalization of every application in the AMetric paper. -/
namespace AASCAMetricMetricUse
noncomputable section
set_option autoImplicit false

def FibreConstant {Z X V : Type} (p : Z → X) (answer : Z → V) : Prop :=
  ∀ z z', p z = p z' → answer z = answer z'

theorem retained_answer_has_unique_descent_iff {Z X V : Type}
    (p : Z → X) (answer : Z → V) :
    (∃! read : Set.range p → V, ∀ z, read ⟨p z,z,rfl⟩ = answer z) ↔
      FibreConstant p answer := by
  constructor
  · rintro ⟨read,commutes,_⟩ z z' same
    exact (commutes z).symm.trans
      ((congrArg read (Subtype.ext same)).trans (commutes z'))
  · intro constant
    let read : Set.range p → V := fun x => answer (Classical.choose x.property)
    have commutes : ∀ z, read ⟨p z,z,rfl⟩ = answer z := by
      intro z
      exact constant _ z (Classical.choose_spec (show ∃ z',p z'=p z from ⟨z,rfl⟩))
    refine ⟨read,commutes,?_⟩
    intro other otherCommutes
    funext x
    obtain ⟨z,hz⟩ := x.property
    have hx : x = (⟨p z,z,rfl⟩ : Set.range p) := Subtype.ext hz.symm
    rw [hx,otherCommutes,commutes]

theorem discordant_fibre_excludes_source_only_answer {Z X V : Type}
    (p : Z → X) (answer : Z → V) (z z' : Z)
    (same : p z=p z') (different : answer z ≠ answer z') :
    ¬ ∃ read : X → V, ∀ a,read (p a)=answer a := by
  rintro ⟨read,commutes⟩
  exact different ((commutes z).symm.trans ((congrArg read same).trans (commutes z')))

def RuleClosed {Judgment : Type} (rules : Set (Set Judgment × Judgment))
    (candidate : Set Judgment) : Prop :=
  ∀ premises conclusion, (premises,conclusion) ∈ rules →
    premises ⊆ candidate → conclusion ∈ candidate

def GroundedClosure {Judgment : Type} (grounds : Set Judgment)
    (rules : Set (Set Judgment × Judgment)) : Set Judgment :=
  {j | ∀ candidate, grounds ⊆ candidate → RuleClosed rules candidate → j ∈ candidate}

theorem grounded_closure_contains_grounds {Judgment : Type}
    (grounds : Set Judgment) (rules : Set (Set Judgment × Judgment)) :
    grounds ⊆ GroundedClosure grounds rules := by
  intro j hj candidate includes _
  exact includes hj

theorem grounded_closure_is_rule_closed {Judgment : Type}
    (grounds : Set Judgment) (rules : Set (Set Judgment × Judgment)) :
    RuleClosed rules (GroundedClosure grounds rules) := by
  intro premises conclusion rule hp candidate includes closed
  apply closed premises conclusion rule
  intro j hj
  exact hp hj candidate includes closed

theorem unseeded_mutual_licenses_are_absent {Judgment : Type}
    (grounds forbidden : Set Judgment) (rules : Set (Set Judgment × Judgment))
    (unseeded : ∀ j,j ∈ grounds → j ∉ forbidden)
    (everyEntrance : ∀ premises conclusion,(premises,conclusion) ∈ rules →
      conclusion ∈ forbidden → ∃ j,j ∈ premises ∧ j ∈ forbidden) :
    ∀ j,j ∈ GroundedClosure grounds rules → j ∉ forbidden := by
  intro j grounded
  apply grounded (forbiddenᶜ) unseeded
  intro premises conclusion rule outside inside
  obtain ⟨k,hk,kin⟩ := everyEntrance premises conclusion rule inside
  exact outside hk kin

theorem independently_grounded_entrance_is_in_closure {Judgment : Type}
    (grounds : Set Judgment) (rules : Set (Set Judgment × Judgment))
    (premises : Set Judgment) (conclusion : Judgment)
    (rule : (premises,conclusion) ∈ rules) (independent : premises ⊆ grounds) :
    conclusion ∈ GroundedClosure grounds rules := by
  apply grounded_closure_is_rule_closed grounds rules premises conclusion rule
  exact fun _ hj => grounded_closure_contains_grounds grounds rules (independent hj)

theorem eligible_equivariant_output_is_stabilizer_fixed
    {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]
    (eligible : X → Set Y) (select : X → Y)
    (inFamily : ∀ x,select x ∈ eligible x)
    (equivariant : ∀ (g : G) x,select (g • x)=g • select x) (x : X) :
    select x ∈ eligible x ∧ ∀ g : G,g • x=x → g • select x=select x := by
  exact ⟨inFamily x,fun g fixed => (equivariant g x).symm.trans (congrArg select fixed)⟩

theorem empty_eligible_fixed_set_excludes_selector
    {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]
    (eligible : X → Set Y) (x : X)
    (empty : ¬ ∃ y,y ∈ eligible x ∧ ∀ g : G,g • x=x → g • y=y) :
    ¬ ∃ select : X → Y,(∀ x,select x ∈ eligible x) ∧
      (∀ (g : G) x,select (g • x)=g • select x) := by
  rintro ⟨select,hf,he⟩
  exact empty ⟨select x,eligible_equivariant_output_is_stabilizer_fixed eligible select hf he x⟩

/-- Output theorem, not an assumed AMetric certificate. No finite rule or
presentation registry is used. Each route retains its own explicit hypotheses. -/
theorem constructed_information_and_grounding_restrictions :
    (∀ (Z X V : Type) (p : Z → X) (answer : Z → V),
      (∃! read : Set.range p → V,∀ z,read ⟨p z,z,rfl⟩=answer z) ↔ FibreConstant p answer) ∧
    (∀ (Judgment : Type) (grounds forbidden : Set Judgment)
      (rules : Set (Set Judgment × Judgment)),
      (∀ j,j ∈ grounds → j ∉ forbidden) →
      (∀ premises conclusion,(premises,conclusion) ∈ rules → conclusion ∈ forbidden →
        ∃ j,j ∈ premises ∧ j ∈ forbidden) →
      ∀ j,j ∈ GroundedClosure grounds rules → j ∉ forbidden) := by
  exact ⟨fun _ _ _ => retained_answer_has_unique_descent_iff,
    fun _ => unseeded_mutual_licenses_are_absent⟩

/-- A conclusion package for the actual Metricity AMetric routes. All clauses
are universally derived here; this predicate is never an input to licensing. -/
def AMetricLicensingDiscipline : Prop :=
  (∀ (Z X V : Type) (p : Z → X) (answer : Z → V),
    (∃! read : Set.range p → V,∀ z,read ⟨p z,z,rfl⟩=answer z) ↔ FibreConstant p answer) ∧
  (∀ (Judgment : Type) (grounds forbidden : Set Judgment) (rules : Set (Set Judgment × Judgment)),
    (∀ j,j ∈ grounds → j ∉ forbidden) →
    (∀ premises conclusion,(premises,conclusion) ∈ rules → conclusion ∈ forbidden →
      ∃ j,j ∈ premises ∧ j ∈ forbidden) →
    ∀ j,j ∈ GroundedClosure grounds rules → j ∉ forbidden) ∧
  (∀ (G X Y : Type) [Group G] [MulAction G X] [MulAction G Y]
    (eligible : X → Set Y) (select : X → Y),
    (∀ x,select x ∈ eligible x) →
    (∀ (g : G) x,select (g • x)=g • select x) →
    ∀ x,select x ∈ eligible x ∧ ∀ g : G,g • x=x → g • select x=select x) ∧
  (∀ (I P Z : Type) [Finite I] (f : (I → P) → Z),
    AASC.KernelReference.EqualityPatterns.Invariant f →
    ∃! read : Quotient (AASC.KernelReference.EqualityPatterns.patternSetoid I P) → Z,
      ∀ x,read (Quotient.mk _ x)=f x) ∧
  (∀ (E Use : Type) (Value : Use → Type)
    (J : AASC.KernelReference.IncidenceNecessity.Incidence E Use Value) (e : E) (q : Use),
    ∃! verdict,AASC.KernelReference.IncidenceNecessity.VerdictIncident J e q verdict)

theorem constructed_ametric_licensing_discipline : AMetricLicensingDiscipline := by
  refine ⟨constructed_information_and_grounding_restrictions.1,
    constructed_information_and_grounding_restrictions.2,?_,?_,?_⟩
  · intro G X Y group actionX actionY eligible select inFamily equivariant x
    exact eligible_equivariant_output_is_stabilizer_fixed eligible select inFamily equivariant x
  · intro I P Z finite f invariant
    exact AASC.KernelReference.EqualityPatterns.invariant_unique_factorization f invariant
  · intro E Use Value J e q
    exact AASC.KernelReference.IncidenceNecessity.complete_assessment_exists_unique J e q

#print axioms FibreConstant
#print axioms retained_answer_has_unique_descent_iff
#print axioms discordant_fibre_excludes_source_only_answer
#print axioms RuleClosed
#print axioms GroundedClosure
#print axioms grounded_closure_contains_grounds
#print axioms grounded_closure_is_rule_closed
#print axioms unseeded_mutual_licenses_are_absent
#print axioms independently_grounded_entrance_is_in_closure
#print axioms eligible_equivariant_output_is_stabilizer_fixed
#print axioms empty_eligible_fixed_set_excludes_selector
#print axioms constructed_information_and_grounding_restrictions
#print axioms AMetricLicensingDiscipline
#print axioms constructed_ametric_licensing_discipline
end
end AASCAMetricMetricUse
