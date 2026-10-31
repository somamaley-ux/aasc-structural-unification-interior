import SourceReachConstruction
import SRLorentzNondegeneracy
import KernelReference.ContextualQuotient

/-! Original increments -> the same completed cone -> constructed Lorentz
form -> exact public Kernel profile descent. Every displacement query of this
cone role is retained. Additional physical roles must be retained by source
refinement; this role quotient is not the whole physical-state quotient.
No metric, ellipsoid or desired metric-factorization field occurs in the input. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set AASC.KernelReference
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem sr_finite_original_reach_convex (W : Set V) :
    Convex ℝ {v|FiniteReach W v} := by
  intro x hx y hy a b ha hb _
  exact FiniteReach.add (FiniteReach.scale a ha hx) (FiniteReach.scale b hb hy)

theorem sr_completed_original_reach_convex (W : Set V) : Convex ℝ (completedReach W) :=
  (sr_finite_original_reach_convex W).closure

theorem sr_original_comparison_preserves_full_completed_cone
    (W : Set V) (h : V ≃L[ℝ] V) (original : h '' W=W) :
    h '' completedReach W=completedReach W := by
  have hforward (w:V) (hw:w∈W):h w∈W:=by
    rw [← original]
    exact ⟨w,hw,rfl⟩
  have hbackward (w:V) (hw:w∈W):h.symm w∈W:=by
    have hm:w∈h '' W:=by rw [original];exact hw
    obtain ⟨v,hv,he⟩:=hm
    simpa only [← he,h.symm_apply_apply] using hv
  have hf:=increment_map_preserves_completedReach W h.toContinuousLinearMap hforward
  have hb:=increment_map_preserves_completedReach W h.symm.toContinuousLinearMap hbackward
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact hf w hw
  · intro hv
    exact ⟨h.symm v,hb v hv,h.apply_symm_apply v⟩

structure SRStructuralConeSource (τ : V →L[ℝ] ℝ) (e : V) (H : Type*) where
  originalIncrements : Set V
  interiorRest : e∈interior (completedReach originalIncrements)
  positiveCompletedClock : ∀ v∈completedReach originalIncrements,v≠0 → 0<τ v
  rest : H → V ≃L[ℝ] V
  preservesOriginal : ∀ h,rest h '' originalIncrements=originalIncrements
  clockPreserved : ∀ h v,τ (rest h v)=τ v
  restFixed : ∀ h,rest h e=e
  boundaryIsotropy :
    ∀ x∈frontier (srCenteredClockBody (completedReach originalIncrements) τ e),
      ∀ y∈frontier (srCenteredClockBody (completedReach originalIncrements) τ e),
      ∃ h,srRestOnClockKernel τ (rest h) (clockPreserved h) x=y

variable (τ : V →L[ℝ] ℝ) [Nontrivial (SRClockSpatialSpace τ)]
  (e : V) (clockOne : τ e=1) {H : Type*}

theorem sr_source_constructs_unique_spatial_lorentz_receipt (s : SRStructuralConeSource τ e H) :
    ∃! G:QuadraticForm ℝ (SRClockSpatialSpace τ),G.PosDef ∧
      (∀ x,x∈srCenteredClockBody (completedReach s.originalIncrements) τ e ↔ G x≤1) ∧
      (∀ h x,G (srRestOnClockKernel τ (s.rest h) (s.clockPreserved h) x)=G x) ∧
      ∀ v,v∈completedReach s.originalIncrements ↔
        0≤τ v ∧ 0≤srConstructedLorentzQuadratic τ e clockOne G v :=
  sr_original_cone_full_isotropy_constructs_unique_spatial_and_lorentz_receipt
    (completedReach s.originalIncrements) isClosed_closure
    (sr_completed_original_reach_convex s.originalIncrements)
    (fun r hr v hv=>smul_mem_completedReach s.originalIncrements r hr hv)
    τ s.positiveCompletedClock e s.interiorRest clockOne s.rest s.clockPreserved s.restFixed
    (fun h=>sr_original_comparison_preserves_full_completed_cone
      s.originalIncrements (s.rest h) (s.preservesOriginal h)) s.boundaryIsotropy

def srSourceSpatialForm (s : SRStructuralConeSource τ e H) :
    QuadraticForm ℝ (SRClockSpatialSpace τ):=
  (sr_source_constructs_unique_spatial_lorentz_receipt τ e clockOne s).choose

theorem sr_source_spatial_positive (s : SRStructuralConeSource τ e H) :
    (srSourceSpatialForm τ e clockOne s).PosDef :=
  (sr_source_constructs_unique_spatial_lorentz_receipt τ e clockOne s).choose_spec.1.1

theorem sr_source_spatial_recovers_full_clock_body (s : SRStructuralConeSource τ e H)
    (x : SRClockSpatialSpace τ) :
    x∈srCenteredClockBody (completedReach s.originalIncrements) τ e ↔
      srSourceSpatialForm τ e clockOne s x≤1 :=
  (sr_source_constructs_unique_spatial_lorentz_receipt τ e clockOne s).choose_spec.1.2.1 x

def srSourceLorentzForm (s : SRStructuralConeSource τ e H) : QuadraticForm ℝ V:=
  srConstructedLorentzQuadratic τ e clockOne (srSourceSpatialForm τ e clockOne s)

theorem sr_source_lorentz_recovers_every_original_completed_query
    (s : SRStructuralConeSource τ e H) (v : V) :
    v∈completedReach s.originalIncrements ↔ 0≤τ v ∧ 0≤srSourceLorentzForm τ e clockOne s v :=
  (sr_source_constructs_unique_spatial_lorentz_receipt τ e clockOne s).choose_spec.1.2.2.2 v

theorem sr_source_constructed_lorentz_nondegenerate (s : SRStructuralConeSource τ e H) :
    (srSourceLorentzForm τ e clockOne s).associated.SeparatingLeft :=
  sr_constructed_lorentz_associated_nondegenerate τ e clockOne _
    (sr_source_spatial_positive τ e clockOne s)

def srOriginalCompletedConeObserve (s : SRStructuralConeSource τ e H) (v : V) : Prop:=
  v∈completedReach s.originalIncrements

theorem sr_source_metric_fibres_are_exact_full_original_cone_profiles
    (s t : SRStructuralConeSource τ e H) :
    srSourceLorentzForm τ e clockOne s=srSourceLorentzForm τ e clockOne t ↔
      ContextualQuotient.Equivalent (srOriginalCompletedConeObserve τ e) s t := by
  constructor
  · intro same v
    apply propext
    change v∈completedReach s.originalIncrements ↔ v∈completedReach t.originalIncrements
    rw [sr_source_lorentz_recovers_every_original_completed_query τ e clockOne s,
      sr_source_lorentz_recovers_every_original_completed_query τ e clockOne t,same]
  · intro same
    have hg:srSourceSpatialForm τ e clockOne s=srSourceSpatialForm τ e clockOne t:=by
      apply sr_positive_quadratic_form_unique_from_full_unit_ball
        _ _ (sr_source_spatial_positive τ e clockOne s) (sr_source_spatial_positive τ e clockOne t)
      intro x
      rw [← sr_source_spatial_recovers_full_clock_body τ e clockOne s,
        ← sr_source_spatial_recovers_full_clock_body τ e clockOne t]
      exact Iff.of_eq (same (e+(x:V)))
    exact congrArg (srConstructedLorentzQuadratic τ e clockOne) hg

theorem sr_source_constructed_metric_unique_injective_public_kernel_descent :
    ∃! reduced:ContextualQuotient.CanonicalQuotient (srOriginalCompletedConeObserve (H:=H) τ e) →
      QuadraticForm ℝ V,
      (∀ s,reduced (ContextualQuotient.classify (srOriginalCompletedConeObserve τ e) s)=
        srSourceLorentzForm τ e clockOne s) ∧ Function.Injective reduced := by
  obtain ⟨reduced,receipt,unique⟩:=ContextualQuotient.unique_factorization
    (srOriginalCompletedConeObserve (H:=H) τ e) (srSourceLorentzForm τ e clockOne)
    (fun s t same=>(sr_source_metric_fibres_are_exact_full_original_cone_profiles τ e clockOne s t).mpr same)
  refine ⟨reduced,⟨receipt,?_⟩,?_⟩
  · intro x y same
    obtain ⟨s,rfl⟩:=ContextualQuotient.classify_surjective (srOriginalCompletedConeObserve τ e) x
    obtain ⟨t,rfl⟩:=ContextualQuotient.classify_surjective (srOriginalCompletedConeObserve τ e) y
    rw [receipt,receipt] at same
    exact (ContextualQuotient.classify_eq_iff _ s t).mpr
      ((sr_source_metric_fibres_are_exact_full_original_cone_profiles τ e clockOne s t).mp same)
  · intro other ho
    exact unique other ho.1

#print axioms sr_finite_original_reach_convex
#print axioms sr_completed_original_reach_convex
#print axioms sr_original_comparison_preserves_full_completed_cone
#print axioms sr_source_constructs_unique_spatial_lorentz_receipt
#print axioms sr_source_spatial_positive
#print axioms sr_source_spatial_recovers_full_clock_body
#print axioms sr_source_lorentz_recovers_every_original_completed_query
#print axioms sr_source_constructed_lorentz_nondegenerate
#print axioms sr_source_metric_fibres_are_exact_full_original_cone_profiles
#print axioms sr_source_constructed_metric_unique_injective_public_kernel_descent
end
end AASCMetricConstruction
