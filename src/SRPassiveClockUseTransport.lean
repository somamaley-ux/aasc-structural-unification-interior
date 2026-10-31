import SRPassiveMarkedClockTransport
import SRLicensedJointReceiver

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

def srPassiveClockUse (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent)
    (c : SRNativeClockUse SRSpace) : SRNativeClockUse SRSpace where
  record := srPassiveClockRecord μ0 A b c.record
  start := srPassiveMarkedTime μ0 A b c.record c.start
  finish := srPassiveMarkedTime μ0 A b c.record c.finish
  claimed := c.claimed

theorem sr_passive_clock_marked_time_preserves_order
    (μ0 : ℝ) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (r : SRClockRecord) (σ ρ : ℝ)
    (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveMarkedTime μ0 A b r σ ≤ srPassiveMarkedTime μ0 A b r ρ ↔ σ ≤ ρ := by
  have rate := (sr_native_clock_reading_rate_positive_bounded μ0 r.2.2 positive).1
  have future := sr_passive_clock_tangent_is_future μ0 source A admitted r.2.2 positive
  have slope := mul_pos rate future
  have difference : srPassiveMarkedTime μ0 A b r ρ - srPassiveMarkedTime μ0 A b r σ =
      (ρ-σ)*(srNativeClockRate μ0 r.2.2*(srPassiveClockTangent μ0 A r.2.2).1) := by
    rw [sr_passive_marked_time_affine μ0 A b r ρ positive,
      sr_passive_marked_time_affine μ0 A b r σ positive]
    dsimp [srMarkedClockProperParameter]
    ring
  constructor
  · intro h
    have nonneg := sub_nonneg.mpr h
    rw [difference] at nonneg
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right slope).mp nonneg)
  · intro h
    apply sub_nonneg.mp
    rw [difference]
    exact mul_nonneg (sub_nonneg.mpr h) slope.le

theorem sr_passive_actual_clock_interval_same
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (c : SRNativeClockUse SRSpace)
    (positive : 0 < srNativeClockMass μ0 c.record.2.2) :
    srNativeClockActualInterval μ0 (srPassiveClockUse μ0 A b c) = srNativeClockActualInterval μ0 c := by
  change (srNativeCoastingMarkedRecord μ0 (srPassiveClockRecord μ0 A b c.record)
      (srPassiveMarkedTime μ0 A b c.record c.finish)).2.reading -
    (srNativeCoastingMarkedRecord μ0 (srPassiveClockRecord μ0 A b c.record)
      (srPassiveMarkedTime μ0 A b c.record c.start)).2.reading = _
  rw [sr_passive_same_marked_clock_reading_square μ0 mass source A admitted b c.record c.finish positive,
    sr_passive_same_marked_clock_reading_square μ0 mass source A admitted b c.record c.start positive]
  rfl

theorem sr_passive_clock_use_has_exact_original_eligibility
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (c : SRNativeClockUse SRSpace) :
    srNativeClockUseValid μ0 (srPassiveClockUse μ0 A b c) ↔ srNativeClockUseValid μ0 c := by
  by_cases positive : 0 < srNativeClockMass μ0 c.record.2.2
  · change (0 < srNativeClockMass μ0 c.record.2.2 ∧
        srPassiveMarkedTime μ0 A b c.record c.start ≤ srPassiveMarkedTime μ0 A b c.record c.finish ∧
        c.claimed = srNativeClockActualInterval μ0 (srPassiveClockUse μ0 A b c)) ↔ _
    rw [sr_passive_clock_marked_time_preserves_order μ0 source A admitted b c.record c.start c.finish positive,
      sr_passive_actual_clock_interval_same μ0 mass source A admitted b c positive]
    rfl
  · change (0 < srNativeClockMass μ0 c.record.2.2 ∧ _) ↔ (0 < srNativeClockMass μ0 c.record.2.2 ∧ _)
    simp only [positive,false_and]

def srClockCertification (μ0 : ℝ) (c : SRNativeClockUse SRSpace) : Option ℝ :=
  if srNativeClockUseValid μ0 c then some c.claimed else none

theorem sr_passive_clock_certification_and_failure_same
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (c : SRNativeClockUse SRSpace) :
    srClockCertification μ0 (srPassiveClockUse μ0 A b c) = srClockCertification μ0 c := by
  simp only [srClockCertification,sr_passive_clock_use_has_exact_original_eligibility μ0 mass source A admitted]
  rfl

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def licensedSRPassiveFrame (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons) (b : SREvent)
    (r : LicensedJointSRReceiver a s Ω) : LicensedJointSRReceiver a s Ω :=
  let j := licensedJointSRSource a s Ω r
  presentLicensedJointSR a s Ω {j with clock := srPassiveClockUse a.mass A b j.clock}
    ((sr_passive_clock_use_has_exact_original_eligibility a.mass a.mass_pos source A admitted b j.clock).mpr
      (licensed_joint_sr_has_actual_valid_source a s Ω r))

theorem licensed_sr_passive_frame_preserves_scalar_preparation
    (source : SRCalibratedFrameSource a.mass) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (r : LicensedJointSRReceiver a s Ω) :
    licensedSRScalar a s Ω (licensedSRPassiveFrame a s Ω source A admitted b r) =
      licensedSRScalar a s Ω r := rfl

theorem licensed_sr_passive_frame_preserves_metric_operand
    (source : SRCalibratedFrameSource a.mass) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (r : LicensedJointSRReceiver a s Ω) :
    (licensedJointSRSource a s Ω (licensedSRPassiveFrame a s Ω source A admitted b r)).metric =
      (licensedJointSRSource a s Ω r).metric := rfl

theorem licensed_sr_passive_frame_preserves_actual_clock_answer
    (source : SRCalibratedFrameSource a.mass) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (r : LicensedJointSRReceiver a s Ω) :
    srClockCertification a.mass
      (licensedJointSRSource a s Ω (licensedSRPassiveFrame a s Ω source A admitted b r)).clock =
        srClockCertification a.mass (licensedJointSRSource a s Ω r).clock :=
  sr_passive_clock_certification_and_failure_same a.mass a.mass_pos source A admitted b _

#print axioms sr_passive_clock_use_has_exact_original_eligibility
#print axioms sr_passive_clock_certification_and_failure_same
#print axioms licensed_sr_passive_frame_preserves_actual_clock_answer
end AASCKleinGordon.CanonicalLicensing.SRIntegration
