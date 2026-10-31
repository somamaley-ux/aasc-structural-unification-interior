import OSRDirectionalClocks
import OSRTimelikeComparison
import SRPassiveClockActionLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

theorem native_frame_preserves_unit (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (U : SREvent) (unit : IsFutureUnit U) : IsFutureUnit (srMatrixFrameEventLinear A U) := by
  have future : IsFutureTimelike U := ⟨unit.1,by rw [unit.2];norm_num⟩
  refine ⟨(native_frame_preserves_future_timelike A admitted U future).1,?_⟩
  rw [native_frame_source_quadratic A admitted,unit.2]

theorem directional_clock_marked_event (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) :
    srMarkedClockEvent mu0 (directionalClockUse mu0 J U origin phase T).record
      (directionalClockUse mu0 J U origin phase T).finish=origin+T • U := by
  have event := directional_clock_actual_event mu0 J positive U unit origin.2 phase origin.1 T
  simpa only [directionalClockUse,srMarkedClockEvent,srNativeCoastingMarkedRecord,add_sub_cancel_left] using event

theorem directional_clock_actual_passive_state (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin b : SREvent) (phase : ℝ) (A : SRMatrixFrame) :
    srPassiveClockState mu0 A b origin.1 (directionalClock mu0 J U origin.2 phase)=
      directionalClock mu0 J (srMatrixFrameEventLinear A U) (frameEvent A b origin).2 phase := by
  apply sr_clock_state_ext
  · rfl
  · change (mu0+J) • (srMatrixFrameEventLinear A (srNativeProperTangent mu0
      (directionalClock mu0 J U origin.2 phase))).2=(mu0+J) • (srMatrixFrameEventLinear A U).2
    rw [directional_clock_actual_proper_tangent mu0 J positive U unit origin.2 phase]
  · rfl
  · rfl

theorem directional_clock_actual_passive_use (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin b : SREvent) (phase T : ℝ) (A : SRMatrixFrame) :
    srPassiveClockUse mu0 A b (directionalClockUse mu0 J U origin phase T)=
      directionalClockUse mu0 J (srMatrixFrameEventLinear A U) (frameEvent A b origin) phase T := by
  apply sr_clock_use_ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact directional_clock_actual_passive_state mu0 J positive U unit origin b phase A
  · change (srMatrixFrameEventLinear A
      (srMarkedClockEvent mu0 (directionalClockUse mu0 J U origin phase T).record origin.1)+b).1=
        (frameEvent A b origin).1
    have start : srMarkedClockEvent mu0 (directionalClockUse mu0 J U origin phase T).record origin.1=origin := by
      simp [directionalClockUse,srMarkedClockEvent,srNativeCoastingMarkedRecord,srNativeClockCoastFlow,directionalClock]
    rw [start]
    rfl
  · change (srMatrixFrameEventLinear A
      (srMarkedClockEvent mu0 (directionalClockUse mu0 J U origin phase T).record
        (directionalClockUse mu0 J U origin phase T).finish)+b).1=
        (frameEvent A b origin).1+T*(srMatrixFrameEventLinear A U).1
    rw [directional_clock_marked_event mu0 J positive U unit origin phase T,map_add,map_smul]
    simp only [frameEvent,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    ring
  · rfl

theorem directional_clock_actual_frame_readout (mu0 J : ℝ) (base : 0 < mu0) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin b : SREvent) (phase T : ℝ) (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) :
    srClockCertification mu0 (directionalClockUse mu0 J (srMatrixFrameEventLinear A U)
      (frameEvent A b origin) phase T)=srClockCertification mu0 (directionalClockUse mu0 J U origin phase T) := by
  rw [←directional_clock_actual_passive_use mu0 J positive U unit origin b phase T A]
  exact sr_passive_clock_certification_and_failure_same mu0 base (srNativeOccupiedFrameSource mu0 base)
    A admitted b _

end AASCKleinGordon.OperationalSR
