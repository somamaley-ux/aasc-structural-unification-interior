import KGWeightedMomentumDynamics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Exact error of the retained original rest-subtracted positive-mass shell.
Only the flat quantum speed is varied; the curved Stage2 parameter stays fixed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter MeasureTheory
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

theorem dispersion_root_ge_mass (a : Parameters) (c : ℝ) (p : Momentum) :
    a.mass ≤ Real.sqrt (a.mass^2 + momentumSq p/c^2) := by
  have h := Real.sqrt_le_sqrt (show a.mass^2 ≤ a.mass^2+momentumSq p/c^2 from
    le_add_of_nonneg_right (div_nonneg (momentumSq_nonneg p) (sq_nonneg c)))
  simpa [Real.sqrt_sq a.mass_pos.le] using h

theorem dispersion_error_algebra (m c q z : ℝ) (hm : m ≠ 0) (hc : c ≠ 0)
    (hz : z+m ≠ 0) (equation : c^2*z^2=c^2*m^2+q) :
    q/(2*m)-q/(z+m)=q^2/(2*m*c^2*(z+m)^2) := by
  field_simp
  linear_combination q * equation

theorem dispersion_error_exact (a : Parameters) (c : ℝ) (hc : 0 < c) (p : Momentum) :
    kgNRKineticEnergy a p - kgNRDispersion a c p =
      momentumSq p ^ 2 /
        (2*a.mass*c^2*(Real.sqrt (a.mass^2+momentumSq p/c^2)+a.mass)^2) := by
  have root := Real.sq_sqrt
    (add_nonneg (sq_nonneg a.mass) (div_nonneg (momentumSq_nonneg p) (sq_nonneg c)))
  have rootScaled : c^2 * (Real.sqrt (a.mass^2+momentumSq p/c^2))^2 =
      c^2*a.mass^2+momentumSq p := by rw [root];field_simp
  exact dispersion_error_algebra a.mass c (momentumSq p) _ a.mass_pos.ne' hc.ne'
    (kg_nr_dispersion_denominator_pos a c p).ne' rootScaled

theorem dispersion_error_nonnegative (a : Parameters) (c : ℝ) (hc : 0 < c) (p : Momentum) :
    0 ≤ kgNRKineticEnergy a p - kgNRDispersion a c p := by
  rw [dispersion_error_exact a c hc p]
  have hm := a.mass_pos
  positivity

theorem dispersion_error_upper (a : Parameters) (c : ℝ) (hc : 0 < c) (p : Momentum) :
    kgNRKineticEnergy a p - kgNRDispersion a c p ≤ momentumSq p^2/(8*a.mass^3*c^2) := by
  rw [dispersion_error_exact a c hc p]
  have hm := a.mass_pos
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  have h := dispersion_root_ge_mass a c p
  have square : (2*a.mass)^2 ≤ (Real.sqrt (a.mass^2+momentumSq p/c^2)+a.mass)^2 := by
    nlinarith [Real.sqrt_nonneg (a.mass^2+momentumSq p/c^2),a.mass_pos]
  have hm := mul_le_mul_of_nonneg_left square (show 0 ≤ 2*a.mass*c^2 by positivity)
  nlinarith

theorem original_energy_error (a : Parameters) (c : ℝ) (hc : 0 < c) (p : Momentum) :
    0 ≤ kgNRKineticEnergy a p - (energy (kgNRParameters a c hc) p - a.mass*c^2) ∧
    kgNRKineticEnergy a p - (energy (kgNRParameters a c hc) p - a.mass*c^2) ≤
      momentumSq p^2/(8*a.mass^3*c^2) := by
  rw [kg_nr_dispersion_is_rest_subtracted_energy]
  exact ⟨dispersion_error_nonnegative a c hc p,dispersion_error_upper a c hc p⟩

theorem phase_difference_bound (a : Parameters) (c : ℝ) (hc : 0 < c) (t : ℝ) (p : Momentum) :
    ‖Translation.phase a.hbar t (kgNRDispersion a c p) -
       Translation.phase a.hbar t (kgNRKineticEnergy a p)‖ ≤
      |t| * momentumSq p^2/(8*a.hbar*a.mass^3*c^2) := by
  have phase_add (r s : ℝ) : Translation.phase a.hbar t (r+s) =
      Translation.phase a.hbar t r * Translation.phase a.hbar t s := by
    unfold Translation.phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have identity : Translation.phase a.hbar t (kgNRDispersion a c p) -
      Translation.phase a.hbar t (kgNRKineticEnergy a p) =
      (Translation.phase a.hbar t (kgNRDispersion a c p-kgNRKineticEnergy a p)-1)*
        Translation.phase a.hbar t (kgNRKineticEnergy a p) := by
    rw [sub_mul,one_mul,←phase_add,sub_add_cancel]
  rw [identity,norm_mul,Translation.phase_norm,mul_one]
  have h := Translation.phase_sub_one_bound a.hbar t (kgNRDispersion a c p-kgNRKineticEnergy a p)
  have habs : |kgNRDispersion a c p-kgNRKineticEnergy a p| =
      kgNRKineticEnergy a p-kgNRDispersion a c p := by
    simpa only [neg_sub] using abs_of_nonpos
      (sub_nonpos.mpr (sub_nonneg.mp (dispersion_error_nonnegative a c hc p)))
  simp only [Real.norm_eq_abs,abs_div,abs_mul,abs_neg,habs,abs_of_pos a.hbar_pos] at h
  refine h.trans ?_
  calc
    |t| * (kgNRKineticEnergy a p-kgNRDispersion a c p)/a.hbar ≤
        |t| * (momentumSq p^2/(8*a.mass^3*c^2))/a.hbar :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (dispersion_error_upper a c hc p) (abs_nonneg t)) a.hbar_pos.le
    _ = _ := by ring

theorem phase_difference_two (a : Parameters) (c t : ℝ) (p : Momentum) :
    ‖Translation.phase a.hbar t (kgNRDispersion a c p) -
       Translation.phase a.hbar t (kgNRKineticEnergy a p)‖ ≤ 2 := by
  simpa only [Translation.phase_norm,show (1:ℝ)+1=2 by norm_num] using
    norm_sub_le (Translation.phase a.hbar t (kgNRDispersion a c p))
      (Translation.phase a.hbar t (kgNRKineticEnergy a p))

end AASCKleinGordon.RecoveryComparison
