import SRSourceConeLineage
import SRExactSourceRefinement

/-! SR 4.8 joined to 5.7: keep the whole old original source profile,
every completed-cone query, and every finite context of the independently
registered partial operations. Construct the Lorentz map only afterwards.
The metric receiver need not distinguish extra original physical roles;
the contextual receiver retains them rather than quotienting them away. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open AASC.KernelReference

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (τ : V →L[ℝ] ℝ) [Nontrivial (SRClockSpatialSpace τ)]
  (e : V) (clockOne : τ e=1) {H : Type}
  {R Old Op : Type} {OldValue : Old → Type}

def srConeRefinementValue (OldValue : Old → Type) : Sum Old V → Type
  | .inl q=>OldValue q
  | .inr _=>Prop

def srConeRefinementOriginalObserve (old : R → (q:Old) → OldValue q)
    (source : R → SRStructuralConeSource τ e H) (r:R) :
    (q:Sum Old V) → srConeRefinementValue (V:=V) OldValue q
  | .inl q=>old r q
  | .inr v=>v∈completedReach (source r).originalIncrements

def srConeFullContextObserve (old : R → (q:Old) → OldValue q)
    (source : R → SRStructuralConeSource τ e H) (operation : Op → R → Option R) :=
  srCompleteOriginalContextObserve (srConeRefinementOriginalObserve τ e old source) operation

theorem sr_constructed_metric_descends_from_full_original_source_contexts
    (old : R → (q:Old) → OldValue q) (source : R → SRStructuralConeSource τ e H)
    (operation : Op → R → Option R) :
    ∃! metric:ContextualQuotient.CanonicalQuotient (srConeFullContextObserve τ e old source operation) →
      QuadraticForm ℝ V,
      ∀ r,metric (ContextualQuotient.classify (srConeFullContextObserve τ e old source operation) r)=
        srSourceLorentzForm τ e clockOne (source r) := by
  apply ContextualQuotient.unique_factorization
  intro r s same
  apply (sr_source_metric_fibres_are_exact_full_original_cone_profiles τ e clockOne (source r) (source s)).mpr
  intro v
  exact same (.original (.inr v))

def srConeRefinementOldForget (old : R → (q:Old) → OldValue q)
    (source : R → SRStructuralConeSource τ e H) (operation : Op → R → Option R) :
    ContextualQuotient.CanonicalQuotient (srConeFullContextObserve τ e old source operation) →
      ContextualQuotient.CanonicalQuotient old :=
  srSourceRefinementForget (srConeRefinementOriginalObserve τ e old source) operation old
    Sum.inl (fun _ _=>id) (fun _ _=>rfl) (fun _ _ _=>rfl)

theorem sr_cone_refinement_preserves_the_attained_old_source
    (old : R → (q:Old) → OldValue q) (source : R → SRStructuralConeSource τ e H)
    (operation : Op → R → Option R) :
    Function.Surjective (srConeRefinementOldForget τ e old source operation) ∧
      ∀ r,srConeRefinementOldForget τ e old source operation
        (ContextualQuotient.classify (srConeFullContextObserve τ e old source operation) r)=
          ContextualQuotient.classify old r := by
  refine ⟨?_,fun _=>rfl⟩
  exact sr_refinement_forget_is_surjective_on_original_attained_domain
    (srConeRefinementOriginalObserve τ e old source) operation old Sum.inl
    (fun _=>id) (fun _ _=>rfl)

theorem sr_original_registered_operations_descend_with_exact_domains_and_outputs
    (old : R → (q:Old) → OldValue q) (source : R → SRStructuralConeSource τ e H)
    (operation : Op → R → Option R) (op:Op) :
    ∃! reduced:ContextualQuotient.CanonicalQuotient (srConeFullContextObserve τ e old source operation) →
      Option (ContextualQuotient.CanonicalQuotient (srConeFullContextObserve τ e old source operation)),
      ∀ r,reduced (ContextualQuotient.classify (srConeFullContextObserve τ e old source operation) r)=
        Option.map (ContextualQuotient.classify (srConeFullContextObserve τ e old source operation))
          (operation op r) :=
  sr_registered_partial_operation_has_unique_exact_context_descent
    (srConeRefinementOriginalObserve τ e old source) operation op

theorem sr_original_context_equivalence_preserves_constructed_metric
    (old : R → (q:Old) → OldValue q) (source : R → SRStructuralConeSource τ e H)
    (operation : Op → R → Option R) (r s:R)
    (lawful : ContextualQuotient.Equivalent (srConeFullContextObserve τ e old source operation) r s) :
    srSourceLorentzForm τ e clockOne (source r)=srSourceLorentzForm τ e clockOne (source s) := by
  apply (sr_source_metric_fibres_are_exact_full_original_cone_profiles τ e clockOne (source r) (source s)).mpr
  intro v
  exact lawful (.original (.inr v))

#print axioms sr_constructed_metric_descends_from_full_original_source_contexts
#print axioms srConeRefinementOldForget
#print axioms sr_cone_refinement_preserves_the_attained_old_source
#print axioms sr_original_registered_operations_descend_with_exact_domains_and_outputs
#print axioms sr_original_context_equivalence_preserves_constructed_metric
end
end AASCMetricConstruction
