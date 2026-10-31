import OSRFrameSupply
import SRProperClockRealization

/-! Inhabited all-direction continuous clocks, from actual native Hamiltonian
states and their complete original coasting records. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def directionalClock (mu0 J : ℝ) (U : SREvent) (x : SRSpace) (phase : ℝ) : SRNativeClockState SRSpace where
  position := x
  momentum := (mu0+J) • U.2
  reading := phase
  internalEnergy := J

theorem directional_clock_actual_mass (mu0 J : ℝ) (U : SREvent) (x : SRSpace) (phase : ℝ) :
    srNativeClockMass mu0 (directionalClock mu0 J U x phase)=mu0+J := rfl

theorem directional_clock_actual_hamiltonian (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase : ℝ) :
    srNativeClockHamiltonian mu0 (directionalClock mu0 J U x phase)=(mu0+J)*U.1 := by
  have h := sr_native_clock_hamiltonian_square mu0 (directionalClock mu0 J U x phase)
  have hp := sr_native_clock_hamiltonian_positive mu0 (directionalClock mu0 J U x phase) positive
  have u : U.1^2-‖U.2‖^2=1 := by rw [←sr_original_order_quadratic_computed];exact unit.2
  change srNativeClockHamiltonian mu0 (directionalClock mu0 J U x phase)^2=
    ‖(mu0+J) • U.2‖^2+(mu0+J)^2 at h
  rw [norm_smul,Real.norm_of_nonneg positive.le] at h
  have scale := congrArg (fun z : ℝ => (mu0+J)^2*z) u
  have rightPositive := mul_pos positive unit.1
  nlinarith

theorem directional_clock_actual_proper_tangent (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase : ℝ) :
    srNativeProperTangent mu0 (directionalClock mu0 J U x phase)=U := by
  apply Prod.ext
  · change srNativeClockHamiltonian mu0 (directionalClock mu0 J U x phase)/(mu0+J)=U.1
    rw [directional_clock_actual_hamiltonian mu0 J positive U unit x phase]
    field_simp
  · change (mu0+J)⁻¹ • ((mu0+J) • U.2)=U.2
    exact inv_smul_smul₀ positive.ne' _

theorem directional_clock_actual_rate (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase : ℝ) :
    srNativeClockRate mu0 (directionalClock mu0 J U x phase)=1/U.1 := by
  unfold srNativeClockRate
  rw [directional_clock_actual_mass,directional_clock_actual_hamiltonian mu0 J positive U unit x phase]
  field_simp

theorem directional_clock_actual_event (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase theta tau : ℝ) :
    (theta+tau*U.1,(srNativeClockCoastFlow mu0 (tau*U.1) (directionalClock mu0 J U x phase)).position)=
      (theta,x)+tau • U := by
  have h := sr_native_actual_coasting_event_in_proper_parameter mu0 theta tau
    (directionalClock mu0 J U x phase) positive
  rw [directional_clock_actual_proper_tangent mu0 J positive U unit x phase] at h
  exact h

theorem directional_clock_actual_reading (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase tau : ℝ) :
    (srNativeClockCoastFlow mu0 (tau*U.1) (directionalClock mu0 J U x phase)).reading=phase+tau := by
  have h := sr_native_actual_coasting_reading_in_proper_parameter mu0 tau
    (directionalClock mu0 J U x phase) positive
  rw [directional_clock_actual_proper_tangent mu0 J positive U unit x phase] at h
  exact h

def directionalClockUse (mu0 J : ℝ) (U origin : SREvent) (phase T : ℝ) : SRNativeClockUse SRSpace where
  record := (0,origin.1,directionalClock mu0 J U origin.2 phase)
  start := origin.1
  finish := origin.1+T*U.1
  claimed := T

theorem directional_clock_use_actual_interval (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) :
    srNativeClockActualInterval mu0 (directionalClockUse mu0 J U origin phase T)=T := by
  rw [sr_native_interval_readout_is_actual_rate]
  change (origin.1+T*U.1-origin.1)*srNativeClockRate mu0 (directionalClock mu0 J U origin.2 phase)=T
  rw [directional_clock_actual_rate mu0 J positive U unit origin.2 phase]
  field_simp [unit.1.ne'] <;> ring

theorem directional_clock_use_actually_valid (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T) :
    srNativeClockUseValid mu0 (directionalClockUse mu0 J U origin phase T) := by
  refine ⟨positive,?_,?_⟩
  · change origin.1 ≤ origin.1+T*U.1
    exact le_add_of_nonneg_right (mul_nonneg forward unit.1.le)
  · exact (directional_clock_use_actual_interval mu0 J positive U unit origin phase T).symm

theorem directional_clock_complete_marked_record (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase tau : ℝ) (id : Fin 2) :
    let record := srNativeCoastingMarkedRecord mu0
      (id,origin.1,directionalClock mu0 J U origin.2 phase) (origin.1+tau*U.1)
    record.1=id ∧ record.2.position=origin.2+tau • U.2 ∧
      record.2.momentum=(mu0+J) • U.2 ∧ record.2.internalEnergy=J ∧ record.2.reading=phase+tau := by
  dsimp only
  refine ⟨rfl,?_,rfl,rfl,?_⟩
  · change (srNativeClockCoastFlow mu0 (origin.1+tau*U.1-origin.1)
      (directionalClock mu0 J U origin.2 phase)).position=origin.2+tau • U.2
    rw [add_sub_cancel_left]
    exact congrArg Prod.snd (directional_clock_actual_event mu0 J positive U unit origin.2 phase origin.1 tau)
  · change (srNativeClockCoastFlow mu0 (origin.1+tau*U.1-origin.1)
      (directionalClock mu0 J U origin.2 phase)).reading=phase+tau
    rw [add_sub_cancel_left]
    exact directional_clock_actual_reading mu0 J positive U unit origin.2 phase tau

end AASCKleinGordon.OperationalSR
