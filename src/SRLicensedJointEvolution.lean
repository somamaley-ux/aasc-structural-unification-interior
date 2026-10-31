import SRPassiveClockActionLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem licensed_joint_source_presentation (r : LicensedJointSRReceiver a s Ω) :
    presentLicensedJointSR a s Ω (licensedJointSRSource a s Ω r)
      (licensed_joint_sr_has_actual_valid_source a s Ω r) = r := by
  obtain ⟨j,v,rfl⟩ := licensed_joint_sr_presentation_coverage a s Ω r
  rfl

theorem licensed_joint_source_injective : Function.Injective (licensedJointSRSource a s Ω) := by
  intro r q same
  rw [← licensed_joint_source_presentation a s Ω r,
    ← licensed_joint_source_presentation a s Ω q]
  congr 1

theorem joint_continuation_preserves_validity (t : JointContinuation)
    (j : JointOriginalSource a s Ω) (valid : srNativeClockUseValid a.mass j.clock) :
    srNativeClockUseValid a.mass (jointContinue a s Ω t j).clock := by
  cases t with
  | inl t => exact valid
  | inr δ => exact sr_native_clock_extension_valid a.mass δ.val j.clock valid δ.property

def licensedJointSRContinue (t : JointContinuation) (r : LicensedJointSRReceiver a s Ω) :
    LicensedJointSRReceiver a s Ω :=
  presentLicensedJointSR a s Ω (jointContinue a s Ω t (licensedJointSRSource a s Ω r))
    (joint_continuation_preserves_validity a s Ω t _
      (licensed_joint_sr_has_actual_valid_source a s Ω r))

theorem licensed_joint_sr_continuation_original_source_square (t : JointContinuation)
    (r : LicensedJointSRReceiver a s Ω) :
    licensedJointSRSource a s Ω (licensedJointSRContinue a s Ω t r) =
      jointContinue a s Ω t (licensedJointSRSource a s Ω r) := rfl

theorem licensed_joint_sr_scalar_continuation_square (t : ℝ) (r : LicensedJointSRReceiver a s Ω) :
    licensedSRScalar a s Ω (licensedJointSRContinue a s Ω (.inl t) r) =
      licensedScalarContinue a s Ω (scalarBaseObject a) t (licensedSRScalar a s Ω r) := rfl

theorem licensed_joint_sr_scalar_continuation_keeps_clock (t σ : ℝ)
    (r : LicensedJointSRReceiver a s Ω) :
    srNativeCoastingMarkedRecord a.mass
      (licensedJointSRSource a s Ω (licensedJointSRContinue a s Ω (.inl t) r)).clock.record σ =
        srNativeCoastingMarkedRecord a.mass (licensedJointSRSource a s Ω r).clock.record σ := rfl

theorem licensed_joint_sr_evolved_original_preparation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (t : ℝ) (r : LicensedJointSRReceiver a s Ω) :
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (licensedSRMetric a s Ω κ Λ coupling (licensedJointSRContinue a s Ω (.inl t) r)))) =
      rayMap _ (kgNRSpatialOriginalPreparation a t
        (licensedScalarPure a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω r))) :=
  common_evolved_original_preparation_square a s Ω κ Λ coupling t
    (licensedSRScalar a s Ω r) (licensedJointSRSource a s Ω r).metric

theorem licensed_joint_sr_clock_continuation_adds_actual_readout
    (δ : {δ : ℝ // 0 ≤ δ}) (r : LicensedJointSRReceiver a s Ω) :
    srNativeClockActualInterval a.mass
      (licensedJointSRSource a s Ω (licensedJointSRContinue a s Ω (.inr δ) r)).clock =
        srNativeClockActualInterval a.mass (licensedJointSRSource a s Ω r).clock +
          δ.val * srNativeClockRate a.mass (licensedJointSRSource a s Ω r).clock.record.2.2 :=
  sr_native_clock_extension_readout_additive a.mass δ.val _

theorem licensed_joint_sr_clock_continuation_keeps_scalar
    (δ : {δ : ℝ // 0 ≤ δ}) (r : LicensedJointSRReceiver a s Ω) :
    licensedSRScalar a s Ω (licensedJointSRContinue a s Ω (.inr δ) r) = licensedSRScalar a s Ω r := rfl

theorem licensed_sr_passive_frame_identity (source : SRCalibratedFrameSource a.mass)
    (r : LicensedJointSRReceiver a s Ω) :
    licensedSRPassiveFrame a s Ω source 1 source.comparisons.one_mem 0 r = r := by
  apply licensed_joint_source_injective a s Ω
  have p := (licensed_joint_sr_has_actual_valid_source a s Ω r).1
  change {licensedJointSRSource a s Ω r with clock := srPassiveClockUse a.mass 1 0 (licensedJointSRSource a s Ω r).clock} = _
  rw [sr_passive_clock_use_identity a.mass _ p]

theorem licensed_sr_passive_frame_composition (source : SRCalibratedFrameSource a.mass)
    (A B : SRMatrixFrame) (ha : A ∈ source.comparisons) (hb : B ∈ source.comparisons)
    (bA bB : SREvent) (r : LicensedJointSRReceiver a s Ω) :
    licensedSRPassiveFrame a s Ω source A ha bA (licensedSRPassiveFrame a s Ω source B hb bB r) =
      licensedSRPassiveFrame a s Ω source (A*B) (source.comparisons.mul_mem ha hb)
        (srMatrixFrameEventLinear A bB+bA) r := by
  apply licensed_joint_source_injective a s Ω
  have p := (licensed_joint_sr_has_actual_valid_source a s Ω r).1
  change {licensedJointSRSource a s Ω r with clock := srPassiveClockUse a.mass A bA (srPassiveClockUse a.mass B bB (licensedJointSRSource a s Ω r).clock)} = _
  rw [sr_passive_clock_use_composition a.mass a.mass_pos source A B hb bA bB _ p]
  rfl

theorem licensed_sr_passive_frame_inverse (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) (b : SREvent)
    (r : LicensedJointSRReceiver a s Ω) :
    licensedSRPassiveFrame a s Ω source A⁻¹ (source.comparisons.inv_mem ha)
      (-srMatrixFrameEventLinear A⁻¹ b) (licensedSRPassiveFrame a s Ω source A ha b r) = r := by
  apply licensed_joint_source_injective a s Ω
  have p := (licensed_joint_sr_has_actual_valid_source a s Ω r).1
  change {licensedJointSRSource a s Ω r with clock := srPassiveClockUse a.mass A⁻¹ (-srMatrixFrameEventLinear A⁻¹ b) (srPassiveClockUse a.mass A b (licensedJointSRSource a s Ω r).clock)} = _
  rw [sr_passive_clock_use_inverse a.mass a.mass_pos source A ha b _ p]

theorem licensed_sr_scalar_evolution_frame_naturality (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) (b : SREvent) (t : ℝ)
    (r : LicensedJointSRReceiver a s Ω) :
    licensedJointSRContinue a s Ω (.inl t) (licensedSRPassiveFrame a s Ω source A ha b r) =
      licensedSRPassiveFrame a s Ω source A ha b (licensedJointSRContinue a s Ω (.inl t) r) := by
  apply licensed_joint_source_injective a s Ω
  rfl

#print axioms licensed_joint_sr_evolved_original_preparation_square
#print axioms licensed_sr_passive_frame_composition
#print axioms licensed_sr_passive_frame_inverse
end AASCKleinGordon.CanonicalLicensing.SRIntegration
