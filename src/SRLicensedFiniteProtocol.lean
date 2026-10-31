import SRJointFrameOperationNaturality
import SRFiniteProtocolFrameTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def jointFiniteProtocolSource (l : ℝ) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) : JointOriginalSource a s Ω :=
  ⟨srOriginalRestTickUse a.mass (2*(N:ℝ)*l),r,H⟩

theorem joint_finite_protocol_source_valid (l : ℝ) (length : 0 < l) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    srNativeClockUseValid a.mass (jointFiniteProtocolSource a s Ω l N r H).clock := by
  refine ⟨?_,?_,?_⟩
  · simpa [jointFiniteProtocolSource,srOriginalRestTickUse,srNativeClockMass,srNativeRestClock] using a.mass_pos
  · change 0 ≤ 2*(N:ℝ)*l
    positivity
  · exact (sr_original_rest_tick_actual_readout a.mass (2*(N:ℝ)*l) a.mass_pos).symm

def licensedJointFiniteProtocol (l : ℝ) (length : 0 < l) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) : LicensedJointSRReceiver a s Ω :=
  presentLicensedJointSR a s Ω (jointFiniteProtocolSource a s Ω l N r H)
    (joint_finite_protocol_source_valid a s Ω l length N r H)

theorem licensed_finite_protocol_source_square (l : ℝ) (length : 0 < l) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    licensedJointSRSource a s Ω (licensedJointFiniteProtocol a s Ω l length N r H) =
      jointFiniteProtocolSource a s Ω l N r H := rfl

theorem licensed_finite_protocol_retains_every_old_preparation (l : ℝ) (length : 0 < l) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    licensedSRScalar a s Ω (licensedJointFiniteProtocol a s Ω l length N r H) = r ∧
      (licensedJointSRSource a s Ω (licensedJointFiniteProtocol a s Ω l length N r H)).metric = H := ⟨rfl,rfl⟩

theorem licensed_finite_protocol_actual_clock_receipt (l : ℝ) (length : 0 < l) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    srClockCertification a.mass
      (licensedJointSRSource a s Ω (licensedJointFiniteProtocol a s Ω l length N r H)).clock =
        some (2*(N:ℝ)*l) := by
  change srClockCertification a.mass (jointFiniteProtocolSource a s Ω l N r H).clock = _
  rw [srClockCertification,if_pos (joint_finite_protocol_source_valid a s Ω l length N r H)]
  rfl

theorem licensed_finite_protocol_every_same_event_return_reading
    (source : SRCalibratedFrameSource a.mass) (F : SROriginalAdmittedFrame a.mass source)
    (l : ℝ) (length : 0 < l) (N : ℕ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) (k : Fin N) :
    let receiver := licensedJointFiniteProtocol a s Ω l length N r H
    let moved := licensedSRPassiveFrame a s Ω source
      (srOriginalFrameUnit F.eventMap F.normalizesOriginalTranslations) F.admitted (F.eventMap 0) receiver
    (srNativeCoastingMarkedRecord a.mass (licensedJointSRSource a s Ω moved).clock.record
      ((F.eventMap (srMarkedClockEvent a.mass (licensedJointSRSource a s Ω receiver).clock.record
        (srNativeProtocolReturn (E:=SRSpace) l k.val).1)).1)).2.reading = 2*((k.val:ℝ)+1)*l := by
  exact sr_every_finite_original_return_tick_has_same_source_frame_reading a.mass a.mass_pos source F l N k

#print axioms joint_finite_protocol_source_valid
#print axioms licensed_finite_protocol_actual_clock_receipt
#print axioms licensed_finite_protocol_every_same_event_return_reading
end AASCKleinGordon.CanonicalLicensing.SRIntegration
