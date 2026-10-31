import SRPassiveClockReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

abbrev SRClockRecord := Fin 2 × (ℝ × SRNativeClockState SRSpace)

def srMarkedClockEvent (μ0 : ℝ) (r : SRClockRecord) (σ : ℝ) : SREvent :=
  (σ,(srNativeCoastingMarkedRecord μ0 r σ).2.position)

def srMarkedClockProperParameter (μ0 : ℝ) (r : SRClockRecord) (σ : ℝ) : ℝ :=
  (σ-r.2.1)*srNativeClockRate μ0 r.2.2

theorem sr_actual_marked_clock_time_from_proper_parameter (μ0 : ℝ) (r : SRClockRecord)
    (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srMarkedClockProperParameter μ0 r σ * (srNativeProperTangent μ0 r.2.2).1 = σ-r.2.1 := by
  have energy := sr_native_clock_hamiltonian_positive μ0 r.2.2 positive
  simp only [srMarkedClockProperParameter,srNativeClockRate,srNativeProperTangent]
  field_simp

theorem sr_actual_marked_clock_event_has_proper_parameter (μ0 : ℝ) (r : SRClockRecord)
    (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srMarkedClockEvent μ0 r σ = (r.2.1,r.2.2.position) +
      srMarkedClockProperParameter μ0 r σ • srNativeProperTangent μ0 r.2.2 := by
  have h := sr_native_actual_coasting_event_in_proper_parameter μ0 r.2.1
    (srMarkedClockProperParameter μ0 r σ) r.2.2 positive
  rw [sr_actual_marked_clock_time_from_proper_parameter μ0 r σ positive] at h
  have sameTime : r.2.1+(σ-r.2.1) = σ := by ring
  rw [sameTime] at h
  exact h

theorem sr_actual_marked_clock_reading_has_proper_parameter (μ0 : ℝ) (r : SRClockRecord)
    (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    (srNativeCoastingMarkedRecord μ0 r σ).2.reading =
      r.2.2.reading+srMarkedClockProperParameter μ0 r σ := by
  have h := sr_native_actual_coasting_reading_in_proper_parameter μ0
    (srMarkedClockProperParameter μ0 r σ) r.2.2 positive
  rw [sr_actual_marked_clock_time_from_proper_parameter μ0 r σ positive] at h
  exact h

theorem sr_actual_marked_event_at_proper_time (μ0 : ℝ) (r : SRClockRecord)
    (τ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srMarkedClockEvent μ0 r (r.2.1+τ*(srNativeProperTangent μ0 r.2.2).1) =
      (r.2.1,r.2.2.position)+τ • srNativeProperTangent μ0 r.2.2 := by
  have h := sr_native_actual_coasting_event_in_proper_parameter μ0 r.2.1 τ r.2.2 positive
  simpa only [srMarkedClockEvent,srNativeCoastingMarkedRecord,add_sub_cancel_left] using h

theorem sr_actual_marked_reading_at_proper_time (μ0 : ℝ) (r : SRClockRecord)
    (τ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    (srNativeCoastingMarkedRecord μ0 r (r.2.1+τ*(srNativeProperTangent μ0 r.2.2).1)).2.reading =
      r.2.2.reading+τ := by
  have h := sr_native_actual_coasting_reading_in_proper_parameter μ0 τ r.2.2 positive
  simpa only [srNativeCoastingMarkedRecord,add_sub_cancel_left] using h

def srPassiveMarkedTime (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent)
    (r : SRClockRecord) (σ : ℝ) : ℝ := (srMatrixFrameEventLinear A (srMarkedClockEvent μ0 r σ)+b).1

theorem sr_passive_actual_event_proper_parameter_square (μ0 : ℝ) (A : SRMatrixFrame)
    (b : SREvent) (r : SRClockRecord) (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srMatrixFrameEventLinear A (srMarkedClockEvent μ0 r σ)+b =
      srPassiveClockOrigin A b r.2.1 r.2.2 +
        srMarkedClockProperParameter μ0 r σ • srPassiveClockTangent μ0 A r.2.2 := by
  rw [sr_actual_marked_clock_event_has_proper_parameter μ0 r σ positive,map_add,map_smul]
  change srMatrixFrameEventLinear A (r.2.1,r.2.2.position) +
    srMarkedClockProperParameter μ0 r σ • srPassiveClockTangent μ0 A r.2.2 + b = _
  dsimp only [srPassiveClockOrigin]
  abel

theorem sr_passive_marked_time_affine (μ0 : ℝ) (A : SRMatrixFrame)
    (b : SREvent) (r : SRClockRecord) (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srPassiveMarkedTime μ0 A b r σ = (srPassiveClockOrigin A b r.2.1 r.2.2).1 +
      srMarkedClockProperParameter μ0 r σ * (srPassiveClockTangent μ0 A r.2.2).1 :=
  congrArg Prod.fst (sr_passive_actual_event_proper_parameter_square μ0 A b r σ positive)

theorem sr_passive_same_marked_clock_event_square
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (r : SRClockRecord) (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    srMarkedClockEvent μ0 (srPassiveClockRecord μ0 A b r) (srPassiveMarkedTime μ0 A b r σ) =
      srMatrixFrameEventLinear A (srMarkedClockEvent μ0 r σ)+b := by
  have tangent := sr_passive_reconstructed_clock_has_transported_proper_tangent
    μ0 mass source A admitted b r.2.1 r.2.2 positive
  have event := sr_actual_marked_event_at_proper_time μ0 (srPassiveClockRecord μ0 A b r)
    (srMarkedClockProperParameter μ0 r σ) positive
  change srMarkedClockEvent μ0 (srPassiveClockRecord μ0 A b r)
    ((srPassiveClockOrigin A b r.2.1 r.2.2).1 +
      srMarkedClockProperParameter μ0 r σ *
        (srNativeProperTangent μ0 (srPassiveClockState μ0 A b r.2.1 r.2.2)).1) = _ at event
  rw [tangent,← sr_passive_marked_time_affine μ0 A b r σ positive] at event
  change srMarkedClockEvent μ0 (srPassiveClockRecord μ0 A b r) (srPassiveMarkedTime μ0 A b r σ) =
    srPassiveClockOrigin A b r.2.1 r.2.2 + srMarkedClockProperParameter μ0 r σ •
      srNativeProperTangent μ0 (srPassiveClockState μ0 A b r.2.1 r.2.2) at event
  rw [tangent] at event
  exact event.trans (sr_passive_actual_event_proper_parameter_square μ0 A b r σ positive).symm

theorem sr_passive_same_marked_clock_reading_square
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (r : SRClockRecord) (σ : ℝ) (positive : 0 < srNativeClockMass μ0 r.2.2) :
    (srNativeCoastingMarkedRecord μ0 (srPassiveClockRecord μ0 A b r)
      (srPassiveMarkedTime μ0 A b r σ)).2.reading =
        (srNativeCoastingMarkedRecord μ0 r σ).2.reading := by
  have tangent := sr_passive_reconstructed_clock_has_transported_proper_tangent
    μ0 mass source A admitted b r.2.1 r.2.2 positive
  have reading := sr_actual_marked_reading_at_proper_time μ0 (srPassiveClockRecord μ0 A b r)
    (srMarkedClockProperParameter μ0 r σ) positive
  change (srNativeCoastingMarkedRecord μ0 (srPassiveClockRecord μ0 A b r)
    ((srPassiveClockOrigin A b r.2.1 r.2.2).1 + srMarkedClockProperParameter μ0 r σ *
      (srNativeProperTangent μ0 (srPassiveClockState μ0 A b r.2.1 r.2.2)).1)).2.reading = _ at reading
  rw [tangent,← sr_passive_marked_time_affine μ0 A b r σ positive] at reading
  exact reading.trans (sr_actual_marked_clock_reading_has_proper_parameter μ0 r σ positive).symm

#print axioms sr_passive_same_marked_clock_event_square
#print axioms sr_passive_same_marked_clock_reading_square
end AASCKleinGordon.CanonicalLicensing.SRIntegration
