import OSRLocalRestLaw
import OSRTimelikeComparison

/-! Conditional classification of an admitted uniform inertial response.
The native Hamiltonian occupant is constructed separately. No homogeneity,
moving calibration or proper-duration formula is a field of this class. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
attribute [local instance] Classical.propDecidable

theorem rest_unit_is_future_unit : IsFutureUnit ((1:ℝ),(0:SRSpace)) := by
  refine ⟨by norm_num,?_⟩
  rw [sr_original_order_quadratic_computed]
  norm_num

structure IdealInertialResponse where
  certified : Set SREvent
  zero_certified : 0 ∈ certified
  future_domain : ∀ w ∈ certified, w=0 ∨ IsFutureTimelike w
  duration : SREvent → ℝ
  positive_readout : ∀ w ∈ certified, IsFutureTimelike w → 0 < duration w
  ray_subdivision : ∀ U : SREvent, IsFutureUnit U → ∀ T : ℝ, 0 ≤ T → T • U ∈ certified →
    ∀ t : ℝ, 0 ≤ t → t ≤ T → t • U ∈ certified
  ray_addition : ∀ U : SREvent, IsFutureUnit U → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    (t+s) • U ∈ certified → duration ((t+s) • U)=duration (t • U)+duration (s • U)
  comparison_available : SRMatrixFrame → SREvent → Prop
  comparison_certified : ∀ A : SRMatrixFrame, A ∈ srNativeFrameComparisons → ∀ w ∈ certified,
    comparison_available A w → srMatrixFrameEventLinear A w ∈ certified
  same_event_readout : ∀ A : SRMatrixFrame, A ∈ srNativeFrameComparisons → ∀ w ∈ certified,
    comparison_available A w → duration (srMatrixFrameEventLinear A w)=duration w
  rest_coverage : ∀ w ∈ certified, IsFutureTimelike w → ∃ A : SRMatrixFrame,
    A ∈ srNativeFrameComparisons ∧ comparison_available A w ∧ (srMatrixFrameEventLinear A w).2=0
  rest_span : ℝ
  rest_span_positive : 0 < rest_span
  rest_span_certified : (rest_span,0) ∈ certified
  rest_calibration : duration (rest_span,0)=rest_span

theorem ideal_duration_zero (D : IdealInertialResponse) : D.duration 0=0 := by
  have h := D.ray_addition (1,0) rest_unit_is_future_unit 0 0 (by norm_num) (by norm_num)
    (by simpa using D.zero_certified)
  simp only [zero_add,zero_smul] at h
  linarith

def idealRestLaw (D : IdealInertialResponse) : LocalRestLaw where
  domain := {t | (t,0) ∈ D.certified}
  zero_mem := D.zero_certified
  domain_nonnegative := by
    intro t ht
    rcases D.future_domain (t,0) ht with zero | future
    · have z := congrArg Prod.fst zero
      change t=0 at z
      exact z.ge
    · exact future.1.le
  subdivision := by
    intro T hT t ht order
    have hTnonnegative : 0 ≤ T := by
      rcases D.future_domain (T,0) hT with zero | future
      · have z := congrArg Prod.fst zero
        change T=0 at z
        exact z.ge
      · exact future.1.le
    have h := D.ray_subdivision (1,0) rest_unit_is_future_unit T hTnonnegative
      (by simpa using hT) t ht order
    simpa using h
  response := fun t => D.duration (t,0)
  response_nonnegative := by
    intro t ht
    rcases D.future_domain (t,0) ht with zero | future
    · rw [zero,ideal_duration_zero]
    · exact (D.positive_readout _ ht future).le
  response_add := by
    intro t s ht hs inside
    have h := D.ray_addition (1,0) rest_unit_is_future_unit t s ht hs (by simpa using inside)
    simpa using h

theorem ideal_rest_response_derived (D : IdealInertialResponse) (t : ℝ) (inside : (t,0) ∈ D.certified) :
    D.duration (t,0)=t :=
  calibrated_local_rest_response_unique (idealRestLaw D) D.rest_span D.rest_span_positive
    D.rest_span_certified D.rest_calibration t inside

theorem ideal_inertial_response_classification (D : IdealInertialResponse)
    (w : SREvent) (inside : w ∈ D.certified) (future : IsFutureTimelike w) :
    D.duration w=restLength w := by
  obtain ⟨A,admitted,available,atRest⟩ := D.rest_coverage w inside future
  have presentation := native_rest_time_is_actual_length A admitted w future atRest
  have restInside := D.comparison_certified A admitted w inside available
  rw [presentation] at restInside
  calc
    D.duration w=D.duration (srMatrixFrameEventLinear A w) :=
      (D.same_event_readout A admitted w inside available).symm
    _ = D.duration (restLength w,0) := congrArg D.duration presentation
    _ = restLength w := ideal_rest_response_derived D _ restInside

theorem ideal_inertial_response_unique (D E : IdealInertialResponse) (w : SREvent)
    (insideD : w ∈ D.certified) (insideE : w ∈ E.certified) (future : IsFutureTimelike w) :
    D.duration w=E.duration w :=
  (ideal_inertial_response_classification D w insideD future).trans
    (ideal_inertial_response_classification E w insideE future).symm

def idealResponseRead (D : IdealInertialResponse) (w : SREvent) : Option ℝ :=
  if w ∈ D.certified then some (D.duration w) else none

theorem ideal_response_read_domain (D : IdealInertialResponse) (w : SREvent) :
    (idealResponseRead D w).isSome=true ↔ w ∈ D.certified := by
  classical
  simp [idealResponseRead]

end AASCKleinGordon.OperationalSR
