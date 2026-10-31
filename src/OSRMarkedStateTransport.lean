import OSRObservationPassive
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint) (n : ℕ)

def transportMarkedState (mu0 : ℝ) (B : SRMatrixFrame) (c : SREvent) (time : ℝ)
    (record : Fin 2 × SRNativeClockState SRSpace) : Fin 2 × SRNativeClockState SRSpace :=
  (record.1,srPassiveClockState mu0 B c time record.2)

theorem passive_full_marked_state_is_actual (mu0 : ℝ) (base : 0 < mu0)
    (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons) (c : SREvent)
    (record : SRClockRecord) (positive : 0 < srNativeClockMass mu0 record.2.2) (time : ℝ) :
    srNativeCoastingMarkedRecord mu0 (srPassiveClockRecord mu0 B c record) (srPassiveMarkedTime mu0 B c record time)=
      transportMarkedState mu0 B c time (srNativeCoastingMarkedRecord mu0 record time) := by
  have event := sr_passive_same_marked_clock_event_square mu0 base (srNativeOccupiedFrameSource mu0 base)
    B admitted c record time positive
  have reading := sr_passive_same_marked_clock_reading_square mu0 base (srNativeOccupiedFrameSource mu0 base)
    B admitted c record time positive
  apply Prod.ext
  · rfl
  · apply sr_clock_state_ext
    · exact congrArg Prod.snd event
    · rfl
    · exact reading
    · rfl


end AASCKleinGordon.OperationalSR
