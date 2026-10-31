import SRCalibratedFrameTheorem
import SRProperClockRealization

/-! Reconstruct the actual Hamiltonian clock record in a proved calibrated
frame. This acts on the same affine worldline and scalar clock reading, with
the transformed initial event's coordinate time retained explicitly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

def srPassiveClockOrigin (A : SRMatrixFrame) (b : SREvent) (θ : ℝ)
    (z : SRNativeClockState SRSpace) : SREvent := srMatrixFrameEventLinear A (θ,z.position)+b

def srPassiveClockTangent (μ0 : ℝ) (A : SRMatrixFrame)
    (z : SRNativeClockState SRSpace) : SREvent :=
  srMatrixFrameEventLinear A (srNativeProperTangent μ0 z)

def srPassiveClockState (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent) (θ : ℝ)
    (z : SRNativeClockState SRSpace) : SRNativeClockState SRSpace where
  position := (srPassiveClockOrigin A b θ z).2
  momentum := srNativeClockMass μ0 z • (srPassiveClockTangent μ0 A z).2
  reading := z.reading
  internalEnergy := z.internalEnergy

def srPassiveClockRecord (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent)
    (r : Fin 2 × (ℝ × SRNativeClockState SRSpace)) : Fin 2 × (ℝ × SRNativeClockState SRSpace) :=
  (r.1,(srPassiveClockOrigin A b r.2.1 r.2.2).1,srPassiveClockState μ0 A b r.2.1 r.2.2)

theorem sr_passive_clock_mass_same (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent) (θ : ℝ)
    (z : SRNativeClockState SRSpace) :
    srNativeClockMass μ0 (srPassiveClockState μ0 A b θ z) = srNativeClockMass μ0 z := rfl

theorem sr_passive_clock_tangent_has_source_derived_unit_norm
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (z : SRNativeClockState SRSpace) (positive : 0 < srNativeClockMass μ0 z) :
    (srPassiveClockTangent μ0 A z).1^2 - ‖(srPassiveClockTangent μ0 A z).2‖^2 = 1 := by
  have preserved := sr_admitted_frames_preserve_same_source_derived_form μ0 mass source A admitted
    (srNativeProperTangent μ0 z)
  rw [sr_original_order_quadratic_computed,sr_original_order_quadratic_computed] at preserved
  exact preserved.trans (sr_native_proper_tangent_unit μ0 z positive)

theorem sr_passive_clock_tangent_is_future
    (μ0 : ℝ) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (z : SRNativeClockState SRSpace) (positive : 0 < srNativeClockMass μ0 z) :
    0 < (srPassiveClockTangent μ0 A z).1 := by
  have unit := sr_native_proper_tangent_unit μ0 z positive
  have future := sr_native_proper_tangent_future μ0 z positive
  have strict : ‖(srNativeProperTangent μ0 z).2‖ < (srNativeProperTangent μ0 z).1 := by
    nlinarith [norm_nonneg (srNativeProperTangent μ0 z).2]
  have image := sr_exact_original_cone_frame_preserves_strict_clock_body
    (srMatrixFrameEvent A) (source.coneReceipt A admitted) (srNativeProperTangent μ0 z) strict
  exact lt_of_le_of_lt (norm_nonneg _) image

theorem sr_passive_reconstructed_clock_has_actual_hamiltonian
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (θ : ℝ) (z : SRNativeClockState SRSpace)
    (positive : 0 < srNativeClockMass μ0 z) :
    srNativeClockHamiltonian μ0 (srPassiveClockState μ0 A b θ z) =
      srNativeClockMass μ0 z * (srPassiveClockTangent μ0 A z).1 := by
  have h := sr_native_clock_hamiltonian_square μ0 (srPassiveClockState μ0 A b θ z)
  have hp := sr_native_clock_hamiltonian_positive μ0 (srPassiveClockState μ0 A b θ z) positive
  have unit := sr_passive_clock_tangent_has_source_derived_unit_norm μ0 mass source A admitted z positive
  have future := sr_passive_clock_tangent_is_future μ0 source A admitted z positive
  change srNativeClockHamiltonian μ0 (srPassiveClockState μ0 A b θ z)^2 =
    ‖srNativeClockMass μ0 z • (srPassiveClockTangent μ0 A z).2‖^2 + srNativeClockMass μ0 z ^ 2 at h
  rw [norm_smul,Real.norm_of_nonneg positive.le] at h
  have scaled := congrArg (fun x : ℝ => srNativeClockMass μ0 z ^ 2 * x) unit
  have rightPositive := mul_pos positive future
  nlinarith

theorem sr_passive_reconstructed_clock_has_transported_proper_tangent
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons)
    (b : SREvent) (θ : ℝ) (z : SRNativeClockState SRSpace)
    (positive : 0 < srNativeClockMass μ0 z) :
    srNativeProperTangent μ0 (srPassiveClockState μ0 A b θ z) = srPassiveClockTangent μ0 A z := by
  apply Prod.ext
  · change srNativeClockHamiltonian μ0 (srPassiveClockState μ0 A b θ z) /
        srNativeClockMass μ0 z = _
    rw [sr_passive_reconstructed_clock_has_actual_hamiltonian μ0 mass source A admitted b θ z positive]
    field_simp
  · change (srNativeClockMass μ0 z)⁻¹ •
      (srNativeClockMass μ0 z • (srPassiveClockTangent μ0 A z).2) = _
    exact inv_smul_smul₀ positive.ne' _

theorem sr_passive_clock_reconstruction_retains_identity_and_internal_reading
    (μ0 : ℝ) (A : SRMatrixFrame) (b : SREvent)
    (r : Fin 2 × (ℝ × SRNativeClockState SRSpace)) :
    (srPassiveClockRecord μ0 A b r).1 = r.1 ∧
      (srPassiveClockRecord μ0 A b r).2.2.reading = r.2.2.reading ∧
      (srPassiveClockRecord μ0 A b r).2.2.internalEnergy = r.2.2.internalEnergy := ⟨rfl,rfl,rfl⟩

#print axioms sr_passive_reconstructed_clock_has_actual_hamiltonian
#print axioms sr_passive_reconstructed_clock_has_transported_proper_tangent
end AASCKleinGordon.CanonicalLicensing.SRIntegration
