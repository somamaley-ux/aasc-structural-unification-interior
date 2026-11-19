import OriginalWardLocalization
import SmoothMinimumEinstein
import OccupiedFullProfileGerms

/-! The occupied Lie readings supply the single curved witness used in the
minimal-order Einstein classification. Its classical differentiated
natural-tensor symmetry input remains explicit. -/
namespace AASCOccupiedProfiles
noncomputable section
open AASCSemanticExhaustion AASCKleinGordon TopologicalSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false

/-- Orders attainable by a natural, active, symmetric metric response closed
on every smooth normalized Lorentz germ. -/
def closedActiveMetricOrders : Set ℕ :=
  {n | ∃ E : MetricFieldResponse,
    SmoothMetricResponseNatural E ∧ SmoothMetricResponseActive E ∧
    (∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i) ∧
    (∀ g, SmoothLorentzOperand g 0 → g 0 = metric →
      (∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0) → coordinateDivergence g (E g) 0 = 0) ∧
    SmoothMetricResponseOrderAtMost E n}

/-- Every finite-order candidate that attains the minimum and reproduces the
original compact Lie readings has precisely one active Einstein coefficient
pair on the smooth metric domain. Neither global geometric closure nor the
value of the minimum is a hypothesis. -/
theorem minimum_response_from_occupied_lie_readings (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0)
    (E : MetricFieldResponse) (n : ℕ)
    (minimum : IsLeast closedActiveMetricOrders n)
    (natural : SmoothMetricResponseNatural E) (order : SmoothMetricResponseOrderAtMost E n)
    (regular : ContDiff ℝ 2 (metricHessianResponseAt E 0))
    (symmetries : NormalResponseSecondSymmetries E)
    (symmetric : ∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i)
    (active : SmoothMetricResponseActive E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E smooth) :
    n = 2 ∧ ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ SmoothEinsteinResponseForm E ac.1 ac.2 := by
  have least : IsLeast closedActiveMetricOrders 2 := least_active_closed_metric_response_order
  have hn : n = 2 := minimum.unique least
  subst n
  have localReadout : SmoothMetricGermLocal E := by
    intro g h p regG regH smG smH near
    refine order g h p ⟨regG.1, smG, regG.2.2⟩ ⟨regH.1, smH, regH.2.2⟩ ⟨?_, ?_⟩
    · exact metric_twojet_of_eventuallyEq g h p near
    · intro k three two
      have bound : k ≤ 2 := by simpa using two
      exact (show ¬ (3 : ℕ) ≤ 2 by decide) (three.trans bound) |>.elim
  have symH (H : AdmittedOperand Ω) : MetricFieldSymmetric (E (originalEHActMetric H.val)) :=
    fun p => symmetric _ p ⟨original_eh_act_metric_symmetric H.val,
      fun i j => (original_eh_act_metric_smooth H.val i j).contDiffAt,
      original_eh_act_metric_frame H.val H.property p⟩
  have cubic := original_lie_readings_close_cubic_witness Ω origin κ Λ hk E localReadout smooth symH reads
  exact ⟨rfl, smooth_minimal_einstein_form_of_cubic_ward E natural order regular symmetries
    symmetric active cubic⟩

end
end AASCOccupiedProfiles
