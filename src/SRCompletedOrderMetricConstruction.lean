import SRGeneralRestClockSeparation
import SRSourceConeLineage

/-! Original completed order, weak duration and actual arbitrary rest action
feed the full SR metric constructor. Strict completed-clock positivity is now
a conclusion, not an input field. Original non-fixed-spatial/isotropy and
continuum-comparison branch conditions remain displayed. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set
open scoped Topology
variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] [Group H]

structure SRCompletedOrderSource (τ:V →L[ℝ] ℝ) (e:V) where
  originalIncrements:Set V
  originalClockNonnegative:∀ w∈originalIncrements,0≤τ w
  completedAntisymmetry:∀ v∈completedReach originalIncrements,
    -v∈completedReach originalIncrements → v=0
  interiorRest:e∈interior (completedReach originalIncrements)
  rest:H →* (V ≃L[ℝ] V)
  preservesOriginal:∀ h,rest h '' originalIncrements=originalIncrements
  clockPreserved:∀ h v,τ (rest h v)=τ v
  restFixed:∀ h,rest h e=e
  noFixedSpatial:∀ v,τ v=0 → (∀ h,rest h v=v) → v=0
  boundaryIsotropy:
    ∀ x∈frontier (srCenteredClockBody (completedReach originalIncrements) τ e),
    ∀ y∈frontier (srCenteredClockBody (completedReach originalIncrements) τ e),
    ∃ h,srRestOnClockKernel τ (rest h) (clockPreserved h) x=y

variable (τ:V →L[ℝ] ℝ) (e:V)

theorem sr_original_completed_order_source_derives_strict_clock
    (s:SRCompletedOrderSource (H:=H) τ e) :
    ∀ v∈completedReach s.originalIncrements,v≠0 → 0<τ v :=
  sr_positive_clock_of_general_original_rest_action
    (completedReach s.originalIncrements) isClosed_closure
    (sr_completed_original_reach_convex s.originalIncrements)
    (zero_mem_completedReach s.originalIncrements)
    (fun u hu v hv=>add_mem_completedReach s.originalIncrements hu hv)
    (fun r hr v hv=>smul_mem_completedReach s.originalIncrements r hr hv)
    s.completedAntisymmetry e s.interiorRest τ
    (weak_clock_extends_to_completedReach s.originalIncrements τ s.originalClockNonnegative)
    s.rest (fun h=>sr_original_comparison_preserves_full_completed_cone
      s.originalIncrements (s.rest h) (s.preservesOriginal h))
    s.clockPreserved s.restFixed s.noFixedSpatial

def srCompletedOrderToConeSource (s:SRCompletedOrderSource (H:=H) τ e) :
    SRStructuralConeSource τ e H where
  originalIncrements:=s.originalIncrements
  interiorRest:=s.interiorRest
  positiveCompletedClock:=sr_original_completed_order_source_derives_strict_clock τ e s
  rest:=fun h=>s.rest h
  preservesOriginal:=s.preservesOriginal
  clockPreserved:=s.clockPreserved
  restFixed:=s.restFixed
  boundaryIsotropy:=s.boundaryIsotropy

theorem sr_completed_order_constructs_unique_full_lorentz_receipt
    [Nontrivial (SRClockSpatialSpace τ)] (clockOne:τ e=1)
    (s:SRCompletedOrderSource (H:=H) τ e) :
    ∃! G:QuadraticForm ℝ (SRClockSpatialSpace τ),G.PosDef ∧
      (∀ x,x∈srCenteredClockBody (completedReach s.originalIncrements) τ e ↔ G x≤1) ∧
      (∀ h x,G (srRestOnClockKernel τ (s.rest h) (s.clockPreserved h) x)=G x) ∧
      ∀ v,v∈completedReach s.originalIncrements ↔
        0≤τ v ∧ 0≤srConstructedLorentzQuadratic τ e clockOne G v :=
  sr_source_constructs_unique_spatial_lorentz_receipt τ e clockOne
    (srCompletedOrderToConeSource τ e s)

theorem sr_completed_order_constructed_lorentz_form_nondegenerate
    [Nontrivial (SRClockSpatialSpace τ)] (clockOne:τ e=1)
    (s:SRCompletedOrderSource (H:=H) τ e) :
    (srSourceLorentzForm τ e clockOne (srCompletedOrderToConeSource τ e s)).associated.SeparatingLeft :=
  sr_source_constructed_lorentz_nondegenerate τ e clockOne (srCompletedOrderToConeSource τ e s)

#print axioms sr_original_completed_order_source_derives_strict_clock
#print axioms srCompletedOrderToConeSource
#print axioms sr_completed_order_constructs_unique_full_lorentz_receipt
#print axioms sr_completed_order_constructed_lorentz_form_nondegenerate
end
end AASCMetricConstruction
