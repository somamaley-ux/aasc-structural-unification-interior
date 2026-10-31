import OSRMarkedStateTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

theorem passive_full_marked_state_composition (mu0 : ℝ) (base : 0 < mu0)
    (B A : SRMatrixFrame) (admittedB : B ∈ srNativeFrameComparisons)
    (admittedA : A ∈ srNativeFrameComparisons) (c b : SREvent)
    (record : SRClockRecord) (positive : 0 < srNativeClockMass mu0 record.2.2) (T : ℝ) :
    srNativeCoastingMarkedRecord mu0
      (srPassiveClockRecord mu0 (B*A) (srMatrixFrameEventLinear B b+c) record)
      (srPassiveMarkedTime mu0 (B*A) (srMatrixFrameEventLinear B b+c) record T)=
    transportMarkedState mu0 B c (srPassiveMarkedTime mu0 A b record T)
      (srNativeCoastingMarkedRecord mu0 (srPassiveClockRecord mu0 A b record)
        (srPassiveMarkedTime mu0 A b record T)) := by
  have recordEq := sr_passive_clock_record_composition mu0 base (srNativeOccupiedFrameSource mu0 base)
    B A admittedA c b record positive
  have timeEq := sr_passive_marked_time_composition mu0 base (srNativeOccupiedFrameSource mu0 base)
    B A admittedA c b record T positive
  have both := congrArg₂ (srNativeCoastingMarkedRecord mu0) recordEq timeEq
  exact both.symm.trans (passive_full_marked_state_is_actual mu0 base B admittedB c
    (srPassiveClockRecord mu0 A b record) positive (srPassiveMarkedTime mu0 A b record T))

end AASCKleinGordon.OperationalSR
