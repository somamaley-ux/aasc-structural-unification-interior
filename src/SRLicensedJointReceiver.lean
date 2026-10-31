import SRJointCanonicalLicensing

/-! Actual maps out of the canonically licensed operational SR receiver.
Scalar NR continuation and clock-window continuation remain distinct tags. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace AASCMetricConstruction
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

abbrev LicensedJointSRReceiver :=
  let D := originalJointSRTask a s Ω
  CanonicalLicensingReceiver D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)

theorem actual_joint_sr_is_safe (j : JointOriginalSource a s Ω)
    (valid : srNativeClockUseValid a.mass j.clock) :
    j ∈ canonicalSafeUses (originalJointSRTask a s Ω) :=
  original_sound_region_is_safe _ _ _ (jointSoundRegion a s Ω)
    (original_joint_sr_region_postfixed a s Ω) j valid

def presentLicensedJointSR (j : JointOriginalSource a s Ω)
    (valid : srNativeClockUseValid a.mass j.clock) : LicensedJointSRReceiver a s Ω :=
  let D := originalJointSRTask a s Ω
  presentSafeOriginalUse D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)
    ⟨j,actual_joint_sr_is_safe a s Ω j valid⟩

def licensedJointSRSource (r : LicensedJointSRReceiver a s Ω) : JointOriginalSource a s Ω :=
  (r.val ()).1.1

theorem licensed_joint_sr_has_actual_valid_source (r : LicensedJointSRReceiver a s Ω) :
    srNativeClockUseValid a.mass (licensedJointSRSource a s Ω r).clock := by
  obtain ⟨x,hx⟩ := r.property
  have safe : x.val ∈ canonicalSafeUses (originalJointSRTask a s Ω) := x.property
  rw [original_safe_uses_are_fixed] at safe
  have valid : srNativeClockUseValid a.mass x.val.clock := safe.1.2.2.1
  have same : licensedJointSRSource a s Ω r = x.val := by
    exact (congrArg (fun p => (p ()).1.1) hx).symm
  rw [same]
  exact valid

theorem licensed_joint_sr_presentation_coverage (r : LicensedJointSRReceiver a s Ω) :
    ∃ j : JointOriginalSource a s Ω, ∃ valid : srNativeClockUseValid a.mass j.clock,
      presentLicensedJointSR a s Ω j valid = r := by
  obtain ⟨x,hx⟩ := r.property
  have safe : x.val ∈ canonicalSafeUses (originalJointSRTask a s Ω) := x.property
  rw [original_safe_uses_are_fixed] at safe
  exact ⟨x.val,safe.1.2.2.1,Subtype.ext hx⟩

def licensedSRRefinement (r : LicensedJointSRReceiver a s Ω) : JointReceiver a s Ω :=
  presentJointOriginal a s Ω (licensedJointSRSource a s Ω r)

def licensedSRScalar (r : LicensedJointSRReceiver a s Ω) :
    LicensedScalarReceiver a s Ω (scalarBaseObject a) := (licensedJointSRSource a s Ω r).scalar

def licensedSRMetric (κ Λ : ℝ) (coupling : κ ≠ 0) (r : LicensedJointSRReceiver a s Ω) :
    LicensedMetricReceiver a s Ω κ Λ :=
  jointToLicensedMetric a s Ω κ Λ coupling (licensedSRRefinement a s Ω r)

theorem licensed_sr_covers_every_scalar_and_metric_preparation
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    ∃ j : LicensedJointSRReceiver a s Ω,
      licensedSRScalar a s Ω j = r ∧ (licensedJointSRSource a s Ω j).metric = H := by
  obtain ⟨j,valid,same⟩ := joint_source_covers_every_old_preparation a s Ω r H
  refine ⟨presentLicensedJointSR a s Ω j valid,?_,?_⟩
  · exact congrArg Prod.fst same
  · exact congrArg Prod.snd same

theorem licensed_sr_same_original_preparation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (j : LicensedJointSRReceiver a s Ω) :
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω (licensedSRMetric a s Ω κ Λ coupling j))) =
      rayMap _ (licensedScalarOriginalPure a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω j)) :=
  common_original_preparation_square a s Ω κ Λ coupling
    (licensedSRScalar a s Ω j) (licensedJointSRSource a s Ω j).metric

theorem licensed_sr_same_metric_operand_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (j : LicensedJointSRReceiver a s Ω) :
    restrictedEHMetric a s Ω (licensedEHResponse a s Ω (licensedSRMetric a s Ω κ Λ coupling j)) =
      originalEHActMetric (licensedJointSRSource a s Ω j).metric.val :=
  common_original_metric_operand_square a s Ω κ Λ coupling
    (licensedSRScalar a s Ω j) (licensedJointSRSource a s Ω j).metric

theorem licensed_sr_complete_old_record_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (j : LicensedJointSRReceiver a s Ω) (q : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (licensedSRMetric a s Ω κ Λ coupling j))) (kgFamilyQuestionInChart q) =
      licensedScalarOutput a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω j) (kgNROldQuestion q) :=
  common_original_metric_source_record_square a s Ω κ Λ coupling
    (licensedSRScalar a s Ω j) (licensedJointSRSource a s Ω j).metric q

theorem licensed_sr_complete_registered_reference_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (j : LicensedJointSRReceiver a s Ω)
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    (licensedReadout a s Ω (licensedSRMetric a s Ω κ Λ coupling j) []).answer
      (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q)) =
      (licensedScalarReference a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω j)
        (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr :=
  common_original_registered_reference_square a s Ω κ Λ coupling
    (licensedSRScalar a s Ω j) (licensedJointSRSource a s Ω j).metric q

#print axioms licensed_joint_sr_has_actual_valid_source
#print axioms licensed_sr_same_original_preparation_square
#print axioms licensed_sr_complete_registered_reference_square
end AASCKleinGordon.CanonicalLicensing.SRIntegration
