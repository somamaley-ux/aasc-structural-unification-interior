import KernelReference.ContextualQuotient

/-! SR 4.7--4.8: exact contextual refinement of original source records.
The original queries, codomains and registered partial operations are fixed
before the receiver. The full finite context grammar retains each operation's
domain and nested failure position. No pairwise domain/output congruence or
desired metric-commutation equation is assumed. Actual physical occupation
and inclusion of the whole original registered repertoire remain source facts.
Finite many-argument one-hole contexts can be registered with fixed shared
operands; this file does not declare an arbitrary selected list complete. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open AASC.KernelReference

inductive SRContextQuery (Base Op : Type)
  | original : Base → SRContextQuery Base Op
  | domain : Op → SRContextQuery Base Op
  | after : Op → SRContextQuery Base Op → SRContextQuery Base Op

def srContextValue {Base Op : Type} (Value : Base → Type) : SRContextQuery Base Op → Type
  | .original q=>Value q
  | .domain _=>Bool
  | .after _ q=>Option (srContextValue Value q)

def srCompleteOriginalContextObserve {R Base Op : Type} {Value : Base → Type}
    (original : R → (q:Base) → Value q) (operation : Op → R → Option R)
    (r:R) : (q:SRContextQuery Base Op) → srContextValue Value q
  | .original q=>original r q
  | .domain op=>(operation op r).isSome
  | .after op q=>Option.map (fun s=>srCompleteOriginalContextObserve original operation s q)
      (operation op r)

theorem sr_complete_contexts_retain_every_original_coordinate
    {R Base Op : Type} {Value : Base → Type}
    (original : R → (q:Base) → Value q) (operation : Op → R → Option R)
    (r:R) (q:Base) :
    ContextualQuotient.readCoordinate (srCompleteOriginalContextObserve original operation)
      (.original q) (ContextualQuotient.classify (srCompleteOriginalContextObserve original operation) r)=
      original r q := rfl

theorem sr_registered_partial_operation_has_unique_exact_context_descent
    {R Base Op : Type} {Value : Base → Type}
    (original : R → (q:Base) → Value q) (operation : Op → R → Option R) (op:Op) :
    ∃! reduced:ContextualQuotient.CanonicalQuotient (srCompleteOriginalContextObserve original operation) →
      Option (ContextualQuotient.CanonicalQuotient (srCompleteOriginalContextObserve original operation)),
      ∀ r,reduced (ContextualQuotient.classify (srCompleteOriginalContextObserve original operation) r)=
        Option.map (ContextualQuotient.classify (srCompleteOriginalContextObserve original operation))
          (operation op r) := by
  apply ContextualQuotient.unique_partial_descent_of_original_contexts
    (srCompleteOriginalContextObserve original operation)
    (srCompleteOriginalContextObserve original operation) (operation op)
  · exact ⟨.domain op,id,fun _=>rfl⟩
  · intro q
    exact ⟨.after op q,id,fun _=>rfl⟩

def srSourceRefinementForget {R Base Op Old : Type} {Value : Base → Type}
    {OldValue : Old → Type} (original : R → (q:Base) → Value q)
    (operation : Op → R → Option R) (old : R → (q:Old) → OldValue q)
    (oldCoordinate : Old → Base) (recover : ∀ r q,Value (oldCoordinate q) → OldValue q)
    (receipt : ∀ r q,recover r q (original r (oldCoordinate q))=old r q)
    (readIndependent : ∀ r s q,recover r q=recover s q) :
    ContextualQuotient.CanonicalQuotient (srCompleteOriginalContextObserve original operation) →
      ContextualQuotient.CanonicalQuotient old :=
  ContextualQuotient.descend (srCompleteOriginalContextObserve original operation)
    (ContextualQuotient.classify old) (by
      intro r s same
      apply (ContextualQuotient.classify_eq_iff old r s).mpr
      intro q
      rw [← receipt r q,← receipt s q,readIndependent r s q]
      exact congrArg (recover s q) (same (.original (oldCoordinate q))))

theorem sr_refinement_forget_original_profile_commutes
    {R Base Op Old : Type} {Value : Base → Type} {OldValue : Old → Type}
    (original : R → (q:Base) → Value q) (operation : Op → R → Option R)
    (old : R → (q:Old) → OldValue q) (oldCoordinate : Old → Base)
    (read : (q:Old) → Value (oldCoordinate q) → OldValue q)
    (receipt : ∀ r q,read q (original r (oldCoordinate q))=old r q) (r:R) :
    srSourceRefinementForget original operation old oldCoordinate (fun _=>read)
      receipt (fun _ _ _=>rfl)
      (ContextualQuotient.classify (srCompleteOriginalContextObserve original operation) r)=
        ContextualQuotient.classify old r := rfl

theorem sr_refinement_forget_is_surjective_on_original_attained_domain
    {R Base Op Old : Type} {Value : Base → Type} {OldValue : Old → Type}
    (original : R → (q:Base) → Value q) (operation : Op → R → Option R)
    (old : R → (q:Old) → OldValue q) (oldCoordinate : Old → Base)
    (read : (q:Old) → Value (oldCoordinate q) → OldValue q)
    (receipt : ∀ r q,read q (original r (oldCoordinate q))=old r q) :
    Function.Surjective (srSourceRefinementForget original operation old oldCoordinate (fun _=>read)
      receipt (fun _ _ _=>rfl)) := by
  intro y
  obtain ⟨r,rfl⟩:=ContextualQuotient.classify_surjective old y
  exact ⟨ContextualQuotient.classify (srCompleteOriginalContextObserve original operation) r,rfl⟩

theorem sr_original_selection_and_failure_are_not_created_by_refinement
    {R Base Op : Type} {Value : Base → Type}
    (original : R → (q:Base) → Value q) (operation : Op → R → Option R)
    (selection : Base) (read : Value selection → Option Bool) :
    (∃ r,read (original r selection)=some true) ↔
      ∃ x:ContextualQuotient.CanonicalQuotient (srCompleteOriginalContextObserve original operation),
        read (ContextualQuotient.readCoordinate (srCompleteOriginalContextObserve original operation)
          (.original selection) x)=some true := by
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨ContextualQuotient.classify (srCompleteOriginalContextObserve original operation) r,hr⟩
  · rintro ⟨x,hx⟩
    obtain ⟨r,rfl⟩:=ContextualQuotient.classify_surjective
      (srCompleteOriginalContextObserve original operation) x
    exact ⟨r,hx⟩

#print axioms sr_complete_contexts_retain_every_original_coordinate
#print axioms sr_registered_partial_operation_has_unique_exact_context_descent
#print axioms srSourceRefinementForget
#print axioms sr_refinement_forget_original_profile_commutes
#print axioms sr_refinement_forget_is_surjective_on_original_attained_domain
#print axioms sr_original_selection_and_failure_are_not_created_by_refinement
end
end AASCMetricConstruction
