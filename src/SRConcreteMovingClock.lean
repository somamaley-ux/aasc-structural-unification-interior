import SRNativeMovingFrameSupply
import SRPassiveClockUseTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open scoped Matrix BigOperators

theorem sr_actual_rest_clock_has_unit_proper_tangent (μ0 : ℝ) (mass : 0 < μ0) :
    srNativeProperTangent μ0 (srNativeRestClock (0:SRSpace)) = (1,0) := by
  have energy : srNativeClockHamiltonian μ0 (srNativeRestClock (0:SRSpace)) = μ0 := by
    simp [srNativeClockHamiltonian,srNativeClockMass,srNativeRestClock,Real.sqrt_sq mass.le]
  apply Prod.ext
  · change srNativeClockHamiltonian μ0 (srNativeRestClock (0:SRSpace)) / (μ0+0) = 1
    rw [energy,add_zero,div_self mass.ne']
  · change (μ0+0)⁻¹ • (0:SRSpace) = 0
    simp

def srConcreteMovingClockState (μ0 : ℝ) : SRNativeClockState SRSpace :=
  srPassiveClockState μ0 srConcreteMovingBoost 0 0 (srNativeRestClock 0)

theorem sr_concrete_moving_clock_tangent_components (μ0 : ℝ) (mass : 0 < μ0) :
    (srPassiveClockTangent μ0 srConcreteMovingBoost (srNativeRestClock 0)).1 = 5/4 ∧
      (srPassiveClockTangent μ0 srConcreteMovingBoost (srNativeRestClock 0)).2 0 = 3/4 := by
  have rest := sr_actual_rest_clock_has_unit_proper_tangent μ0 mass
  constructor
  · change (srMatrixFrameEventLinear srConcreteMovingBoost (srNativeProperTangent μ0 (srNativeRestClock 0))).1 = _
    rw [rest]
    simpa using sr_unit_axial_boost_time (5/4) (3/4) (by norm_num) (1,0)
  · change (srMatrixFrameEventLinear srConcreteMovingBoost (srNativeProperTangent μ0 (srNativeRestClock 0))).2 0 = _
    rw [rest]
    have h := congrArg (fun v : CoordinatePoint => v 1)
      (sr_event_frame_coordinate_square srConcreteMovingBoost (1,0))
    have probe : srEventCoordinates (1,0) = originalComparisonProbe 0 := by
      ext i
      fin_cases i <;> rfl
    change (srMatrixFrameEventLinear srConcreteMovingBoost (1,0)).2 0 = _ at h
    rw [probe] at h
    exact h.trans sr_native_comparison_family_contains_genuine_moving_frame.2

theorem sr_native_actual_moving_clock_energy_momentum_and_rate (μ0 : ℝ) (mass : 0 < μ0) :
    srNativeClockMass μ0 (srConcreteMovingClockState μ0) = μ0 ∧
      srNativeClockHamiltonian μ0 (srConcreteMovingClockState μ0) = μ0*(5/4) ∧
      (srConcreteMovingClockState μ0).momentum 0 = μ0*(3/4) ∧
      srNativeClockRate μ0 (srConcreteMovingClockState μ0) = 4/5 := by
  have positive : 0 < srNativeClockMass μ0 (srNativeRestClock (0:SRSpace)) := by
    simpa [srNativeClockMass,srNativeRestClock] using mass
  have tangent := sr_concrete_moving_clock_tangent_components μ0 mass
  have energy := sr_passive_reconstructed_clock_has_actual_hamiltonian μ0 mass
    (srNativeOccupiedFrameSource μ0 mass) srConcreteMovingBoost
    sr_native_comparison_family_contains_genuine_moving_frame.1 0 0 (srNativeRestClock 0) positive
  change srNativeClockHamiltonian μ0 (srConcreteMovingClockState μ0) =
    (μ0+0)*(srPassiveClockTangent μ0 srConcreteMovingBoost (srNativeRestClock 0)).1 at energy
  rw [add_zero,tangent.1] at energy
  refine ⟨?_,energy,?_,?_⟩
  · change μ0+0 = μ0
    exact add_zero _
  · change (μ0+0) * (srPassiveClockTangent μ0 srConcreteMovingBoost (srNativeRestClock 0)).2 0 = _
    rw [add_zero,tangent.2]
  · change (μ0+0) / srNativeClockHamiltonian μ0 (srConcreteMovingClockState μ0) = _
    rw [add_zero,energy]
    field_simp [mass.ne']

#print axioms sr_native_actual_moving_clock_energy_momentum_and_rate
end AASCKleinGordon.CanonicalLicensing.SRIntegration
