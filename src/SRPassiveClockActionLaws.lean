import SRPassiveClockUseTransport
import SRNativeFrameOccupation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

theorem sr_clock_state_ext (z w : SRNativeClockState SRSpace)
    (position : z.position=w.position) (momentum : z.momentum=w.momentum)
    (reading : z.reading=w.reading) (internal : z.internalEnergy=w.internalEnergy) : z=w := by
  cases z
  cases w
  simp_all

theorem sr_clock_use_ext (c d : SRNativeClockUse SRSpace)
    (record : c.record=d.record) (start : c.start=d.start)
    (finish : c.finish=d.finish) (claimed : c.claimed=d.claimed) : c=d := by
  cases c
  cases d
  simp_all

theorem sr_passive_clock_record_identity (μ0 : ℝ) (r : SRClockRecord)
    (positive : 0 < srNativeClockMass μ0 r.2.2) : srPassiveClockRecord μ0 1 0 r = r := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change (srMatrixFrameEventLinear 1 (r.2.1,r.2.2.position)+0).1 = r.2.1
      rw [sr_event_frame_one,add_zero]
    · apply sr_clock_state_ext
      · change (srMatrixFrameEventLinear 1 (r.2.1,r.2.2.position)+0).2 = r.2.2.position
        rw [sr_event_frame_one,add_zero]
      · change srNativeClockMass μ0 r.2.2 •
          (srMatrixFrameEventLinear 1 (srNativeProperTangent μ0 r.2.2)).2 = r.2.2.momentum
        rw [sr_event_frame_one]
        change srNativeClockMass μ0 r.2.2 • ((srNativeClockMass μ0 r.2.2)⁻¹ • r.2.2.momentum) = _
        exact smul_inv_smul₀ positive.ne' _
      · rfl
      · rfl

theorem sr_passive_clock_origin_composition (μ0 : ℝ) (A B : SRMatrixFrame)
    (bA bB : SREvent) (r : SRClockRecord) :
    srPassiveClockOrigin A bA (srPassiveClockRecord μ0 B bB r).2.1
      (srPassiveClockRecord μ0 B bB r).2.2 =
        srPassiveClockOrigin (A*B) (srMatrixFrameEventLinear A bB+bA) r.2.1 r.2.2 := by
  change srMatrixFrameEventLinear A (srMatrixFrameEventLinear B (r.2.1,r.2.2.position)+bB)+bA = _
  rw [map_add,← sr_event_frame_mul]
  dsimp [srPassiveClockOrigin]
  abel

theorem sr_passive_clock_tangent_composition
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A B : SRMatrixFrame) (admittedB : B ∈ source.comparisons)
    (bB : SREvent) (r : SRClockRecord) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveClockTangent μ0 A (srPassiveClockRecord μ0 B bB r).2.2 =
      srPassiveClockTangent μ0 (A*B) r.2.2 := by
  change srMatrixFrameEventLinear A (srNativeProperTangent μ0 (srPassiveClockState μ0 B bB r.2.1 r.2.2)) = _
  rw [sr_passive_reconstructed_clock_has_transported_proper_tangent μ0 mass source B admittedB bB r.2.1 r.2.2 positive]
  exact (sr_event_frame_mul A B _).symm

theorem sr_passive_clock_record_composition
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A B : SRMatrixFrame) (admittedB : B ∈ source.comparisons)
    (bA bB : SREvent) (r : SRClockRecord) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveClockRecord μ0 A bA (srPassiveClockRecord μ0 B bB r) =
      srPassiveClockRecord μ0 (A*B) (srMatrixFrameEventLinear A bB+bA) r := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrArg (fun z : SREvent => z.1) (sr_passive_clock_origin_composition μ0 A B bA bB r)
    · apply sr_clock_state_ext
      · exact congrArg (fun z : SREvent => z.2) (sr_passive_clock_origin_composition μ0 A B bA bB r)
      · change srNativeClockMass μ0 r.2.2 •
          (srPassiveClockTangent μ0 A (srPassiveClockRecord μ0 B bB r).2.2).2 = _
        rw [sr_passive_clock_tangent_composition μ0 mass source A B admittedB bB r positive]
        rfl
      · rfl
      · rfl

theorem sr_passive_marked_time_identity (μ0 : ℝ) (r : SRClockRecord) (σ : ℝ) :
    srPassiveMarkedTime μ0 1 0 r σ = σ := by
  simp [srPassiveMarkedTime,sr_event_frame_one,srMarkedClockEvent]

theorem sr_passive_marked_time_composition
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A B : SRMatrixFrame) (admittedB : B ∈ source.comparisons)
    (bA bB : SREvent) (r : SRClockRecord) (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveMarkedTime μ0 A bA (srPassiveClockRecord μ0 B bB r) (srPassiveMarkedTime μ0 B bB r σ) =
      srPassiveMarkedTime μ0 (A*B) (srMatrixFrameEventLinear A bB+bA) r σ := by
  change (srMatrixFrameEventLinear A
      (srMarkedClockEvent μ0 (srPassiveClockRecord μ0 B bB r) (srPassiveMarkedTime μ0 B bB r σ))+bA).1 =
    (srMatrixFrameEventLinear (A*B) (srMarkedClockEvent μ0 r σ)+(srMatrixFrameEventLinear A bB+bA)).1
  rw [sr_passive_same_marked_clock_event_square μ0 mass source B admittedB bB r σ positive,
    map_add,← sr_event_frame_mul]
  congr 1
  abel

theorem sr_passive_clock_use_identity (μ0 : ℝ) (c : SRNativeClockUse SRSpace)
    (positive : 0 < srNativeClockMass μ0 c.record.2.2) : srPassiveClockUse μ0 1 0 c = c := by
  apply sr_clock_use_ext
  · exact sr_passive_clock_record_identity μ0 c.record positive
  · exact sr_passive_marked_time_identity μ0 c.record c.start
  · exact sr_passive_marked_time_identity μ0 c.record c.finish
  · rfl

theorem sr_passive_clock_use_composition
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A B : SRMatrixFrame) (admittedB : B ∈ source.comparisons)
    (bA bB : SREvent) (c : SRNativeClockUse SRSpace) (positive : 0 < srNativeClockMass μ0 c.record.2.2) :
    srPassiveClockUse μ0 A bA (srPassiveClockUse μ0 B bB c) =
      srPassiveClockUse μ0 (A*B) (srMatrixFrameEventLinear A bB+bA) c := by
  apply sr_clock_use_ext
  · exact sr_passive_clock_record_composition μ0 mass source A B admittedB bA bB c.record positive
  · exact sr_passive_marked_time_composition μ0 mass source A B admittedB bA bB c.record c.start positive
  · exact sr_passive_marked_time_composition μ0 mass source A B admittedB bA bB c.record c.finish positive
  · rfl

theorem sr_passive_clock_use_inverse
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (c : SRNativeClockUse SRSpace) (positive : 0 < srNativeClockMass μ0 c.record.2.2) :
    srPassiveClockUse μ0 A⁻¹ (-srMatrixFrameEventLinear A⁻¹ b) (srPassiveClockUse μ0 A b c) = c := by
  rw [sr_passive_clock_use_composition μ0 mass source A⁻¹ A admitted,
    inv_mul_cancel,add_neg_cancel,sr_passive_clock_use_identity μ0 c positive]
  exact positive

#print axioms sr_passive_clock_record_composition
#print axioms sr_passive_clock_use_composition
#print axioms sr_passive_clock_use_inverse
end AASCKleinGordon.CanonicalLicensing.SRIntegration
