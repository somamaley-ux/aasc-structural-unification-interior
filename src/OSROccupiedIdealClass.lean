import OSRNativeIdealResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

theorem actual_native_ideal_class_is_occupied (mu0 J : ℝ) (base : 0 < mu0) (positive : 0 < mu0+J) :
    ∃ D : IdealInertialResponse, D.duration=nativeDuration mu0 J ∧ D.certified=nativeCertified ∧
      ∀ w : SREvent, w ∈ D.certified → IsFutureTimelike w →
        D.duration w=restLength w ∧ srNativeClockUseValid mu0 (nativeIntervalUse mu0 J w) ∧
        srNativeClockActualInterval mu0 (nativeIntervalUse mu0 J w)=D.duration w ∧
        srMarkedClockEvent mu0 (nativeIntervalUse mu0 J w).record (nativeIntervalUse mu0 J w).finish=w := by
  refine ⟨nativeIdealResponse mu0 J base positive,rfl,rfl,?_⟩
  intro w inside future
  refine ⟨ideal_inertial_response_classification (nativeIdealResponse mu0 J base positive) w inside future,?_⟩
  exact native_duration_has_actual_original_use mu0 J positive w future

end AASCKleinGordon.OperationalSR
