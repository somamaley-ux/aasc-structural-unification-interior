import EinsteinOriginalCurvatureResponse
import KGScalarComparatorFourier
import SRCalibratedFrameTheorem

/-!
# Coverage of an independently specified physical task

An original candidate can have a different type from the objects classified by
a projection theorem. Coverage requires a qualified representative with the same
answers to the original observations. The three applications below specify those
answers and retain coverage as an explicit hypothesis.
-/

set_option autoImplicit false

namespace AASCProjectionCoverage

/-- Any property of the recorded answers transfers along faithful coverage.
The answer type may be an entire family of observations. No representative
needs to be unique, and the hypotheses do not require the task to be occupied. -/
theorem forall_of_faithful_coverage {Original Representative Answer : Type*}
    (qualified : Original → Prop) (admitted : Representative → Prop)
    (originalAnswer : Original → Answer) (read : Representative → Answer)
    (covered : ∀ x, qualified x → ∃ r, admitted r ∧ originalAnswer x = read r)
    (law : Answer → Prop) (classified : ∀ r, admitted r → law (read r)) :
    ∀ x, qualified x → law (originalAnswer x) := by
  intro x hx
  obtain ⟨r, hr, same⟩ := covered x hx
  rw [same]
  exact classified r hr

section Gravity
open AASCSemanticExhaustion

/-- A metric response is observed only at a regular Lorentzian metric and point. -/
abbrev RegularMetricQuery :=
  { q : MetricField × CoordinatePoint // C2LorentzMetricAt q.1 q.2 }

def regularMetricReadout (E : MetricFieldResponse) (q : RegularMetricQuery) : Tensor2 :=
  E q.val.1 q.val.2

/-- The six geometric inputs of the regular first-curvature classification. -/
def geometricFirstResponse (E : MetricFieldResponse) : Prop :=
  RegularLorentzResponseNatural E ∧ RegularLorentzTwoJetLocal E ∧
    OriginalCurvatureFirstResponse E ∧
    (∀ g p, C2LorentzMetricAt g p → ∀ i j, E g p i j = E g p j i) ∧
    GeneralNormalMetricResponseClosure E ∧ FullLorentzEnvelopeResponseActive E

noncomputable def einsteinReadout (ac : ℝ × ℝ) (q : RegularMetricQuery) : Tensor2 :=
  let g := q.val.1
  let p := q.val.2
  ac.1 • (coordinateRicci g p - (1 / 2 : ℝ) • coordinateScalarMetric g p) + ac.2 • g p

private theorem regular_readout_eq_iff (E : MetricFieldResponse) (ac : ℝ × ℝ) :
    regularMetricReadout E = einsteinReadout ac ↔ CoordinateEinsteinResponseForm E ac.1 ac.2 := by
  constructor
  · intro h g p B hsym hreg hB
    exact congrFun h ⟨(g, p), hsym, hreg, B, hB⟩
  · intro h
    funext q
    obtain ⟨B, hB⟩ := q.property.2.2
    exact h q.val.1 q.val.2 B q.property.1 q.property.2.1 hB

/-- Coefficient uniqueness holds for the whole family of regular observations
of each covered candidate. The coefficient pair can depend on the candidate. -/
theorem einstein_of_faithful_coverage {Original : Type*} (qualified : Original → Prop)
    (answers : Original → RegularMetricQuery → Tensor2)
    (covered : ∀ x, qualified x →
      ∃ E, geometricFirstResponse E ∧ answers x = regularMetricReadout E) :
    ∀ x, qualified x → ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ answers x = einsteinReadout ac := by
  apply forall_of_faithful_coverage qualified geometricFirstResponse answers regularMetricReadout covered
    (fun f => ∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧ f = einsteinReadout ac)
  intro E h
  obtain ⟨natural, locality, first, symmetric, closure, active⟩ := h
  obtain ⟨ac, ⟨nonzero, form⟩, unique⟩ :=
    original_curvature_general_response_has_unique_einstein_form E natural locality first
      symmetric closure active
  refine ⟨ac, ⟨nonzero, (regular_readout_eq_iff E ac).2 form⟩, ?_⟩
  intro bc other
  exact unique bc ⟨other.1, (regular_readout_eq_iff E bc).1 other.2⟩
end Gravity

section Quantum
open AASCKleinGordon

/-- The original answers specify all input-output pairs of the spatial generator.
This includes its domain. The calibration is on the comparator's symbol. -/
theorem schrodinger_of_faithful_coverage {Original : Type*} (a : Parameters)
    (qualified : Original → Prop)
    (answers : Original → Set (KGNRSpatialHilbert × KGNRSpatialHilbert))
    (covered : ∀ x, qualified x →
      ∃ (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert) (C : KGScalarFreeComparator H),
        KGFreeAnchoredDispersionAt a C ∧ answers x = (H.graph : Set _)) :
    ∀ x, qualified x → answers x = ((kgNRSpatialKinetic a).graph : Set _) := by
  let admitted := fun (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert) =>
    ∃ C : KGScalarFreeComparator H, KGFreeAnchoredDispersionAt a C
  refine forall_of_faithful_coverage qualified admitted answers (fun H => (H.graph : Set _)) ?_
    (fun graph => graph = ((kgNRSpatialKinetic a).graph : Set _)) ?_
  · intro x hx
    obtain ⟨H, C, calibration, same⟩ := covered x hx
    exact ⟨H, ⟨C, calibration⟩, same⟩
  · intro H hH
    obtain ⟨C, calibration⟩ := hH
    rw [kg_free_calibrated_comparator_eq a C calibration]
end Quantum

section Relativity
open AASCMetricConstruction AASCMetricConstruction.SRIntegration
open AASCKleinGordon.CanonicalLicensing.SRIntegration

/-- Coverage compares the actual event-increment maps before asking about any
quadratic reading. Interval invariance then follows from the calibrated source. -/
theorem lorentz_of_faithful_coverage {Original : Type*} (mass : ℝ) (positive : 0 < mass)
    (source : SRCalibratedFrameSource mass) (qualified : Original → Prop)
    (transform : Original → SREvent → SREvent)
    (covered : ∀ x, qualified x → ∃ A ∈ source.comparisons,
      transform x = srMatrixFrameEvent A) :
    ∀ x, qualified x → ∀ z, srOriginalOrderQuadratic (transform x z) =
        srOriginalOrderQuadratic z := by
  apply forall_of_faithful_coverage qualified (fun A => A ∈ source.comparisons) transform
    (fun A z => srMatrixFrameEvent A z) covered
    (fun f => ∀ z, srOriginalOrderQuadratic (f z) = srOriginalOrderQuadratic z)
  intro A hA z
  exact sr_admitted_frames_preserve_same_source_derived_form mass positive source A hA z

/-- Doubling every event increment transports the entire native future cone
onto itself. It changes the reconstructed quadratic reading of a unit rest
increment, exhibiting the scale freedom before a rest tick is fixed. -/
theorem dilation_preserves_cone_changes_rest_interval :
    (fun z : SREvent => (2 : ℝ) • z) '' srRayFutureCone = srRayFutureCone ∧
      srOriginalOrderQuadratic ((2 : ℝ) • ((1, 0) : SREvent)) ≠
        srOriginalOrderQuadratic ((1, 0) : SREvent) := by
  have cone {t : ℝ} (ht : 0 < t) (z : SREvent) :
      t • z ∈ srRayFutureCone ↔ z ∈ srRayFutureCone := by
    change ‖t • z.2‖ ≤ t * z.1 ↔ ‖z.2‖ ≤ z.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_iff_right₀ ht
  constructor
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (cone (by norm_num : (0 : ℝ) < 2) w).2 hw
    · intro hz
      refine ⟨(1 / 2 : ℝ) • z, (cone (by norm_num : (0 : ℝ) < 1 / 2) z).2 hz, ?_⟩
      change (2 : ℝ) • ((1 / 2 : ℝ) • z) = z
      rw [smul_smul]
      norm_num
  · rw [sr_original_order_quadratic_computed, sr_original_order_quadratic_computed]
    norm_num
end Relativity

#print axioms forall_of_faithful_coverage
#print axioms einstein_of_faithful_coverage
#print axioms schrodinger_of_faithful_coverage
#print axioms lorentz_of_faithful_coverage
#print axioms dilation_preserves_cone_changes_rest_interval

end AASCProjectionCoverage
