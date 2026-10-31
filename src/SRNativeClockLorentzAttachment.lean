import SRNativeFiniteReflectionProtocol
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual coasting functions satisfy the clock flow equations; their reading
rate matches the independently constructed full cone form. The Hamiltonian is
the explicit physical model law of SR 15.3, not derived from bare Kernel. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sr_native_actual_coasting_position_derivative (μ0:ℝ) (z:SRNativeClockState E) (t:ℝ) :
    HasDerivAt (fun s:ℝ=>(srNativeClockCoastFlow μ0 s z).position)
      (srNativeClockVelocity μ0 z) t := by
  simpa only [one_smul] using ((hasDerivAt_id t).smul_const (srNativeClockVelocity μ0 z)).const_add z.position

theorem sr_native_actual_coasting_reading_derivative (μ0:ℝ) (z:SRNativeClockState E) (t:ℝ) :
    HasDerivAt (fun s:ℝ=>(srNativeClockCoastFlow μ0 s z).reading)
      (srNativeClockRate μ0 z) t := by
  simpa only [one_mul] using ((hasDerivAt_id t).mul_const (srNativeClockRate μ0 z)).const_add z.reading

theorem sr_native_clock_internal_hamiltonian_derivative (μ0:ℝ) (z:SRNativeClockState E)
    (positive:0<srNativeClockMass μ0 z) :
    HasDerivAt (fun J:ℝ=>Real.sqrt (‖z.momentum‖^2+(μ0+J)^2))
      (srNativeClockRate μ0 z) z.internalEnergy := by
  have hp:=sr_native_clock_hamiltonian_positive μ0 z positive
  have ha:‖z.momentum‖^2+(μ0+z.internalEnergy)^2≠0:=by
    have hmass:0<μ0+z.internalEnergy:=positive
    nlinarith [sq_nonneg ‖z.momentum‖]
  have hh:= (Real.hasDerivAt_sqrt ha).comp z.internalEnergy
    ((hasDerivAt_const z.internalEnergy (‖z.momentum‖^2)).add
      (((hasDerivAt_id z.internalEnergy).const_add μ0).pow 2))
  convert hh using 1 <;> try rfl
  change srNativeClockMass μ0 z/srNativeClockHamiltonian μ0 z=
    (1/(2*srNativeClockHamiltonian μ0 z))*(0+2*(srNativeClockMass μ0 z)^(2-1)*1)
  field_simp
  <;> ring

theorem sr_native_clock_rate_matches_full_constructed_lorentz_form
    (μ0:ℝ) (z:SRNativeClockState E) (positive:0<srNativeClockMass μ0 z) :
    srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E)) (srOccupiedIsotropicRaySource (E:=E))
      (1,srNativeClockVelocity μ0 z)=(srNativeClockRate μ0 z)^2 := by
  have hp:=sr_native_clock_hamiltonian_positive μ0 z positive
  have hs:=sr_native_clock_hamiltonian_square μ0 z
  have hn:‖srNativeClockVelocity μ0 z‖=(srNativeClockHamiltonian μ0 z)⁻¹*‖z.momentum‖:=by
    rw [srNativeClockVelocity,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp]
  rw [sr_full_ray_source_constructor_computes_lorentz_form_everywhere]
  change 1^2-‖srNativeClockVelocity μ0 z‖^2=(srNativeClockRate μ0 z)^2
  rw [hn,srNativeClockRate]
  field_simp
  <;> nlinarith

#print axioms sr_native_actual_coasting_position_derivative
#print axioms sr_native_actual_coasting_reading_derivative
#print axioms sr_native_clock_internal_hamiltonian_derivative
#print axioms sr_native_clock_rate_matches_full_constructed_lorentz_form
end
end AASCMetricConstruction
