import OSRDirectionalClocks
import SRLicensedJointReceiver

/-! Actual occupied clock states enter the original canonical licensing and
common scalar/EH receiver through the original constructors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint)

def directionalJointSource (J : ℝ) (U origin : SREvent) (phase T : ℝ)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) : JointOriginalSource a s Omega :=
  ⟨directionalClockUse a.mass J U origin phase T,r,H⟩

theorem directional_joint_actual_valid (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) :
    srNativeClockUseValid a.mass (directionalJointSource a s Omega J U origin phase T r H).clock :=
  directional_clock_use_actually_valid a.mass J positive U unit origin phase T forward

def licensedDirectionalClock (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) : LicensedJointSRReceiver a s Omega :=
  presentLicensedJointSR a s Omega (directionalJointSource a s Omega J U origin phase T r H)
    (directional_joint_actual_valid a s Omega J positive U unit origin phase T forward r H)

theorem licensed_directional_actual_source (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) :
    licensedJointSRSource a s Omega (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)=
      directionalJointSource a s Omega J U origin phase T r H := rfl

theorem licensed_directional_original_preparations (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) :
    licensedSRScalar a s Omega (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)=r ∧
      (licensedJointSRSource a s Omega (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)).metric=H :=
  ⟨rfl,rfl⟩

theorem directional_actual_canonical_license (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}) :
    constructedLicensing (originalJointSRTask a s Omega)
      (directionalJointSource a s Omega J U origin phase T r H) (originalJointSRUseMeaning a s Omega) :=
  actual_joint_sr_use_has_canonical_license a s Omega _
    (directional_joint_actual_valid a s Omega J positive U unit origin phase T forward r H)

theorem directional_actual_eh_operand (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    restrictedEHMetric a s Omega (licensedEHResponse a s Omega
      (licensedSRMetric a s Omega kappa Lambda coupling
        (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)))=
      originalEHActMetric H.val :=
  licensed_sr_same_metric_operand_square a s Omega kappa Lambda coupling _

theorem directional_actual_registered_reference (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (q : RegisteredQuestion (KGFamilyQuestion a Omega (kgOriginalObject a))) :
    (licensedReadout a s Omega (licensedSRMetric a s Omega kappa Lambda coupling
      (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)) []).answer
        (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q))=
      (licensedScalarReference a s Omega (scalarBaseObject a) r (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr :=
  licensed_sr_complete_registered_reference_square a s Omega kappa Lambda coupling _ q

end AASCKleinGordon.OperationalSR
