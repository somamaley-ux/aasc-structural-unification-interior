import OccupiedMinimumEinstein

/-! Minimize among the finite-order candidates that preserve the *measured*
Lie readings on every bounded operand. An action or closed-tensor certificate
is not a prerequisite for membership. The reference response realizes the
observations through the same integral tensor readout used for rivals. -/
namespace AASCOccupiedProfiles
noncomputable section
open AASCSemanticExhaustion AASCKleinGordon TopologicalSpace
open AASCKleinGordon.CanonicalLicensing
open scoped Topology ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false

theorem original_eh_realizes_occupied_lie_readings (Ω : Opens CoordinatePoint)
    (κ Λ : ℝ) (hk : κ ≠ 0) :
    ∃ smooth : ∀ H : AdmittedOperand Ω,
        SmoothCoordinateMetric (originalEHGeometricResponse κ Λ (originalEHActMetric H.val)),
      AllOriginalLieReadings Ω κ Λ (originalEHGeometricResponse κ Λ) smooth := by
  have smooth (H : AdmittedOperand Ω) :
      SmoothCoordinateMetric (originalEHGeometricResponse κ Λ (originalEHActMetric H.val)) := by
    let g := originalEHActMetric H.val
    have hg := original_eh_act_metric_smooth H.val
    have neg := original_eh_act_metric_negative H.val H.property
    intro i j
    have eqf : (fun x => originalEHGeometricResponse κ Λ g x i j) =
        (fun x => -(1/κ) * ((coordinateRicci g x i j -
          (coordinateScalarCurvature g x / 2) * g x i j) + Λ * g x i j)) :=
      funext (fun x => congrArg (fun M : Tensor2 => M i j)
        (eh_original_geometric_tensor_identified κ Λ hk g x (neg x)))
    rw [eqf, contDiff_iff_contDiffAt]
    exact fun p => contDiffAt_const.mul (((eh_actual_ricci_smooth_at g hg p (ne_of_lt (neg p)) i j).sub
      ((eh_actual_scalar_curvature_smooth_at g hg p (ne_of_lt (neg p))).div_const 2 |>.mul
        (hg i j).contDiffAt)).add (contDiffAt_const.mul (hg i j).contDiffAt))
  refine ⟨smooth, ?_⟩
  intro H
  let g := originalEHActMetric H.val
  let W := occupiedTensorReadout H (originalEHGeometricResponse κ Λ g) (smooth H)
  let V := operandOriginalReading κ Λ hk H
  have repW := occupied_tensor_readout_represents H (originalEHGeometricResponse κ Λ g) (smooth H)
  have repV : RepresentsMetricTensor g (originalEHGeometricResponse κ Λ g) V := fun i φ =>
    eh_original_geometric_tensor_represents_action_source κ Λ hk g
      (original_eh_act_metric_symmetric H.val) (original_eh_act_metric_smooth H.val) _ i φ
  have same : representedMetricSource W = representedMetricSource V := by
    funext i
    apply ContinuousLinearMap.ext
    intro φ
    exact (repW i φ).trans (repV i φ).symm
  apply (occupied_lie_readings_iff_same_current κ Λ hk H W).mpr
  rw [same]

/-- A genuine hierarchy of responses that pass the original derivative
comparisons. All finite orders are initially available. -/
def originalLieResponseOrders (Ω : Opens CoordinatePoint) (κ Λ : ℝ) : Set ℕ :=
  {n | ∃ E : MetricFieldResponse, SmoothMetricResponseNatural E ∧ SmoothMetricResponseActive E ∧
    (∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i) ∧
    SmoothMetricResponseOrderAtMost E n ∧
    ∃ smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)),
      AllOriginalLieReadings Ω κ Λ E smooth}

theorem original_lie_observations_least_order (Ω : Opens CoordinatePoint)
    (κ Λ : ℝ) (hk : κ ≠ 0) : IsLeast (originalLieResponseOrders Ω κ Λ) 2 := by
  constructor
  · let E := originalEHGeometricResponse κ Λ
    have hn := eh_original_geometric_response_regular_natural κ Λ hk
    have hl := eh_original_geometric_response_twojet_local κ Λ hk
    have active := smooth_activity_of_regular_two_jet_activity E hn hl
      (eh_original_geometric_full_envelope_active κ Λ hk)
    refine ⟨E, original_eh_natural_under_smooth_coordinates κ Λ hk, active, ?_,
      (occupied_eh_least_intrinsic_order κ Λ hk).1,
      original_eh_realizes_occupied_lie_readings Ω κ Λ hk⟩
    intro g p hg
    exact eh_original_geometric_response_symmetric κ Λ hk g p
      ⟨hg.1, fun i j => (hg.2.1 i j).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)), hg.2.2⟩
  · rintro n ⟨E, natural, active, _, order, _⟩
    exact active_natural_response_order_lower_bound E natural active n order

/-- The minimized class is specified by the observed readings themselves.
The coefficient conclusion retains the smooth Lovelock symmetry interface. -/
theorem einstein_form_at_observed_minimum (Ω : Opens CoordinatePoint)
    (origin : (0 : CoordinatePoint) ∈ Ω) (κ Λ : ℝ) (hk : κ ≠ 0)
    (E : MetricFieldResponse) (n : ℕ) (minimum : IsLeast (originalLieResponseOrders Ω κ Λ) n)
    (natural : SmoothMetricResponseNatural E) (order : SmoothMetricResponseOrderAtMost E n)
    (regular : ContDiff ℝ 2 (metricHessianResponseAt E 0)) (symmetries : NormalResponseSecondSymmetries E)
    (symmetric : ∀ g p, SmoothLorentzOperand g p → ∀ i j, E g p i j = E g p j i)
    (active : SmoothMetricResponseActive E)
    (smooth : ∀ H : AdmittedOperand Ω, SmoothCoordinateMetric (E (originalEHActMetric H.val)))
    (reads : AllOriginalLieReadings Ω κ Λ E smooth) :
    n = 2 ∧ ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ SmoothEinsteinResponseForm E ac.1 ac.2 := by
  have num := minimum.unique (original_lie_observations_least_order Ω κ Λ hk)
  subst n
  exact minimum_response_from_occupied_lie_readings Ω origin κ Λ hk E 2
    least_active_closed_metric_response_order natural order regular symmetries symmetric active smooth reads

end
end AASCOccupiedProfiles
