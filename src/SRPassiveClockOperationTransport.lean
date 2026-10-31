import SRPassiveClockActionLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

def srPassiveClockSlope (μ0 : ℝ) (A : SRMatrixFrame) (z : SRNativeClockState SRSpace) : ℝ :=
  srNativeClockRate μ0 z * (srPassiveClockTangent μ0 A z).1

theorem sr_passive_clock_slope_positive (μ0 : ℝ) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons) (z : SRNativeClockState SRSpace)
    (positive : 0 < srNativeClockMass μ0 z) : 0 < srPassiveClockSlope μ0 A z :=
  mul_pos (sr_native_clock_reading_rate_positive_bounded μ0 z positive).1
    (sr_passive_clock_tangent_is_future μ0 source A admitted z positive)

theorem sr_passive_marked_time_increment (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent)
    (r : SRClockRecord) (σ δ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveMarkedTime μ0 A b r (σ+δ) =
      srPassiveMarkedTime μ0 A b r σ + srPassiveClockSlope μ0 A r.2.2 * δ := by
  rw [sr_passive_marked_time_affine μ0 A b r (σ+δ) positive,
    sr_passive_marked_time_affine μ0 A b r σ positive]
  dsimp [srMarkedClockProperParameter,srPassiveClockSlope]
  ring

theorem sr_passive_clock_rate_slope_identity (μ0 : ℝ) (mass : 0 < μ0)
    (source : SRCalibratedFrameSource μ0) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (r : SRClockRecord)
    (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srNativeClockRate μ0 (srPassiveClockRecord μ0 A b r).2.2 *
      srPassiveClockSlope μ0 A r.2.2 = srNativeClockRate μ0 r.2.2 := by
  have energy := sr_passive_reconstructed_clock_has_actual_hamiltonian
    μ0 mass source A admitted b r.2.1 r.2.2 positive
  have future := sr_passive_clock_tangent_is_future μ0 source A admitted r.2.2 positive
  change srNativeClockMass μ0 r.2.2 /
    srNativeClockHamiltonian μ0 (srPassiveClockState μ0 A b r.2.1 r.2.2) *
      (srNativeClockRate μ0 r.2.2 * (srPassiveClockTangent μ0 A r.2.2).1) = _
  rw [energy]
  field_simp [positive.ne',future.ne']

theorem sr_passive_clock_record_rebase (μ0 : ℝ) (mass : 0 < μ0)
    (source : SRCalibratedFrameSource μ0) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (r : SRClockRecord) (h : ℝ)
    (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveClockRecord μ0 A b (srNativeClockRedescription μ0 h r) =
      srNativeClockRedescription μ0 (srPassiveClockSlope μ0 A r.2.2*h)
        (srPassiveClockRecord μ0 A b r) := by
  have time := sr_passive_marked_time_affine μ0 A b r (r.2.1+h) positive
  have time' : srPassiveMarkedTime μ0 A b r (r.2.1+h) =
      (srPassiveClockRecord μ0 A b r).2.1+srPassiveClockSlope μ0 A r.2.2*h := by
    rw [time]
    dsimp [srMarkedClockProperParameter,srPassiveClockSlope,srPassiveClockRecord]
    ring
  have event := sr_passive_same_marked_clock_event_square μ0 mass source A admitted b r (r.2.1+h) positive
  have reading := sr_passive_same_marked_clock_reading_square μ0 mass source A admitted b r (r.2.1+h) positive
  rw [time'] at event reading
  have eventPos := congrArg (fun e : SREvent => e.2) event
  have eventTime := congrArg (fun e : SREvent => e.1) event
  simp only [srMarkedClockEvent,srNativeCoastingMarkedRecord,add_sub_cancel_left] at eventPos eventTime reading
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact eventTime.symm
    · apply sr_clock_state_ext
      · exact eventPos.symm
      · rfl
      · exact reading.symm
      · rfl

theorem sr_passive_marked_time_rebase (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent)
    (r : SRClockRecord) (h σ : ℝ) :
    srPassiveMarkedTime μ0 A b (srNativeClockRedescription μ0 h r) σ =
      srPassiveMarkedTime μ0 A b r σ := by
  simp only [srPassiveMarkedTime,srMarkedClockEvent,
    sr_native_clock_redescription_preserves_every_original_marked_record]

theorem sr_passive_clock_use_rebase (μ0 : ℝ) (mass : 0 < μ0)
    (source : SRCalibratedFrameSource μ0) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (c : SRNativeClockUse SRSpace) (h : ℝ)
    (positive : 0 < srNativeClockMass μ0 c.record.2.2) :
    srPassiveClockUse μ0 A b (srNativeClockUseRedescription μ0 h c) =
      srNativeClockUseRedescription μ0 (srPassiveClockSlope μ0 A c.record.2.2*h)
        (srPassiveClockUse μ0 A b c) := by
  apply sr_clock_use_ext
  · exact sr_passive_clock_record_rebase μ0 mass source A admitted b c.record h positive
  · exact sr_passive_marked_time_rebase μ0 A b c.record h c.start
  · exact sr_passive_marked_time_rebase μ0 A b c.record h c.finish
  · rfl

theorem sr_passive_clock_use_extension (μ0 : ℝ) (mass : 0 < μ0)
    (source : SRCalibratedFrameSource μ0) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (b : SREvent) (c : SRNativeClockUse SRSpace) (δ : ℝ)
    (positive : 0 < srNativeClockMass μ0 c.record.2.2) :
    srPassiveClockUse μ0 A b (srNativeExtendClockUse μ0 δ c) =
      srNativeExtendClockUse μ0 (srPassiveClockSlope μ0 A c.record.2.2*δ)
        (srPassiveClockUse μ0 A b c) := by
  apply sr_clock_use_ext
  · rfl
  · rfl
  · exact sr_passive_marked_time_increment μ0 A b c.record c.finish δ positive
  · change srNativeClockActualInterval μ0 (srNativeExtendClockUse μ0 δ c) =
      srNativeClockActualInterval μ0
        (srNativeExtendClockUse μ0 (srPassiveClockSlope μ0 A c.record.2.2*δ)
          (srPassiveClockUse μ0 A b c))
    rw [sr_native_clock_extension_readout_additive,sr_native_clock_extension_readout_additive,
      sr_passive_actual_clock_interval_same μ0 mass source A admitted b c positive]
    have rate := sr_passive_clock_rate_slope_identity μ0 mass source A admitted b c.record positive
    change srNativeClockRate μ0 (srPassiveClockUse μ0 A b c).record.2.2 *
      srPassiveClockSlope μ0 A c.record.2.2 = srNativeClockRate μ0 c.record.2.2 at rate
    nlinarith [congrArg (fun t : ℝ => δ*t) rate]

#print axioms sr_passive_clock_use_rebase
#print axioms sr_passive_clock_use_extension
end AASCKleinGordon.CanonicalLicensing.SRIntegration
