import KernelReference.IncidenceNecessity
import Mathlib.Tactic

/-! Scope audit of adopted Metricity 2.8/2.12/5.1/5.2/6.2/6.5.
These predicates expose the missing native order instance. No physical first
interface, earlier-use exclusion, or domain interpretation is asserted as an
axiom, certificate field, or output. The two countermodels concern invalid
logical implications, not an occupied physical model of the whole corpus. -/
namespace AASCMetricityOrderAudit
noncomputable section
set_option autoImplicit false

inductive DescriptorSector where
  | distance | topology | causal | dynamics | observation | constantPresentation

/-- Arbitrary original payload families, not a finite enumeration of descriptors.
Duration belongs in the original distance-sector payload and cannot be omitted. -/
abbrev FullDescriptorFamily (original : DescriptorSector → Type) := Sigma original

def DeclaredStep {C T : Type} (R : C → T → C → Prop) (c d : C) : Prop := ∃ t, R c t d

/-- Every reachable node and outgoing original edge is checked. Required
availability belongs in AD, as in the manuscript, even if no edge is present. -/
def OriginalSafe {C T : Type} (AD : C → Prop) (R W : C → T → C → Prop) (c : C) : Prop :=
  ∀ d, Relation.ReflTransGen (DeclaredStep R) c d → AD d ∧ ∀ t e, R d t e → W d t e

def MetricAvailable {I M C T : Type} (useAt : I → M → C → Prop)
    (AD : C → Prop) (R W : C → T → C → Prop) (p : I) : Prop :=
  ∃ m c, useAt p m c ∧ OriginalSafe AD R W c

/-- Exactly the native target still requiring an independently interpreted
physical prerequisite order and complete original descriptor/use family. -/
def LocalMetricBoundary {I M C T : Type} [Preorder I] (Bplace p : I)
    (useAt : I → M → C → Prop) (AD : C → Prop) (R W : C → T → C → Prop) : Prop :=
  Bplace ≤ p ∧ MetricAvailable useAt AD R W p ∧
    ∀ q, q < p → ¬ MetricAvailable useAt AD R W q

theorem earlier_original_use_refutes_later_first_availability
    {I M C T : Type} [Preorder I] (Bplace p q : I)
    (useAt : I → M → C → Prop) (AD : C → Prop) (R W : C → T → C → Prop)
    (earlier : q < p) (m : M) (c : C) (interpreted : useAt q m c)
    (safe : OriginalSafe AD R W c) : ¬ LocalMetricBoundary Bplace p useAt AD R W := by
  intro boundary
  exact boundary.2.2 q earlier ⟨m,c,interpreted,safe⟩

/-- The exact source-supported implication of Metricity 4.2 / AMetric 7.2.
The discordant pair is explicit; this does not manufacture one for a physical predecessor. -/
theorem discordant_original_fibre_excludes_that_source_only_answer
    {Z X V : Type} (p : Z → X) (w : Z → V) (z z' : Z)
    (same : p z = p z') (different : w z ≠ w z') :
    ¬ ∃ reader : X → V, ∀ a, reader (p a) = w a := by
  rintro ⟨reader,hreader⟩
  apply different
  exact (hreader z).symm.trans ((congrArg reader same).trans (hreader z'))

/-- Loss of a richer complete answer does not imply loss of nonconstant duration.
Only a retained-content countermodel; it creates no physical clock or license. -/
theorem lost_richer_answer_does_not_exclude_retained_duration :
    (¬ ∃ reader : ℝ → ℝ × Bool, ∀ z : ℝ × Bool, reader z.1 = z) ∧
    (∃ duration : ℝ → ℝ, (∀ z : ℝ × Bool, duration z.1 = z.1) ∧ duration 0 ≠ duration 1) := by
  constructor
  · exact discordant_original_fibre_excludes_that_source_only_answer Prod.fst id
      (0,false) (0,true) rfl (by simp)
  · exact ⟨id,fun _ => rfl,by norm_num⟩

open AASC.KernelReference

/-- An independently fixed original relation, prior to qualification reporting. -/
def groundedOriginalIncidence : IncidenceNecessity.Incidence Unit Unit (fun _ => Bool) :=
  fun _ _ v => v = true

def groundedLocalCondition (_ : Unit) : Prop :=
  IncidenceNecessity.Qualified groundedOriginalIncidence () ()

def groundedTransitions (_ : Unit) (_ : Unit) (_ : Unit) : Prop := True
def groundedWarrants (_ : Unit) (_ : Unit) (_ : Unit) : Prop := True

theorem original_incidence_supplies_qualification_and_safe_record :
    IncidenceNecessity.assess groundedOriginalIncidence () () = true ∧
      OriginalSafe groundedLocalCondition groundedTransitions groundedWarrants () := by
  constructor
  · exact IncidenceNecessity.actual_incidence_gives_positive (J := groundedOriginalIncidence)
      (e := ()) (q := ()) (value := true) rfl
  · intro _ _
    exact ⟨⟨true,rfl⟩,fun _ _ _ => trivial⟩

/-- An order/availability fragment: every positive interface supports every
original descriptor. This is not an interpretation of the actual physical order. -/
def positiveInterfaceUse {M : Type} (p : ℝ) (_ : M) (_ : Unit) : Prop := 0 < p

theorem nonempty_grounded_safe_uses_do_not_force_a_minimal_interface
    {M : Type} (duration : M) :
    (∃ p : ℝ, MetricAvailable (@positiveInterfaceUse M)
      groundedLocalCondition groundedTransitions groundedWarrants p) ∧
    ¬ ∃ p : ℝ, LocalMetricBoundary 0 p (@positiveInterfaceUse M)
      groundedLocalCondition groundedTransitions groundedWarrants := by
  have hs := original_incidence_supplies_qualification_and_safe_record.2
  constructor
  · exact ⟨1,duration,(),by norm_num [positiveInterfaceUse],hs⟩
  · rintro ⟨p,boundary⟩
    obtain ⟨m,c,hp,_⟩ := boundary.2.1
    have hpos : 0 < p := hp
    have half : p/2 < p := by linarith
    exact boundary.2.2 (p/2) half ⟨m,c,by change 0 < p/2; linarith,hs⟩

#print axioms FullDescriptorFamily
#print axioms OriginalSafe
#print axioms MetricAvailable
#print axioms LocalMetricBoundary
#print axioms earlier_original_use_refutes_later_first_availability
#print axioms discordant_original_fibre_excludes_that_source_only_answer
#print axioms lost_richer_answer_does_not_exclude_retained_duration
#print axioms original_incidence_supplies_qualification_and_safe_record
#print axioms nonempty_grounded_safe_uses_do_not_force_a_minimal_interface
end
end AASCMetricityOrderAudit
