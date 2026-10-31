import L2TranslationPhase
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
open Filter
open scoped Topology
namespace AASCKleinGordon.Translation

def coefficient (hbar : ℝ) : ℂ := -Complex.I/(hbar : ℂ)

def phaseSlope (hbar t r : ℝ) : ℂ := ((t⁻¹ : ℝ) : ℂ)*(phase hbar t r-1)

theorem phase_hasDerivAt_zero (hbar r : ℝ) :
    HasDerivAt (fun t => phase hbar t r) (coefficient hbar*(r : ℂ)) 0 := by
  have h := ((((hasDerivAt_id (0 : ℝ)).neg.mul_const r).div_const hbar).ofReal_comp.mul_const
    Complex.I).cexp
  convert h using 1
  simp [coefficient] <;> ring

theorem phaseSlope_tendsto (hbar r : ℝ) :
    Tendsto (fun t => phaseSlope hbar t r) (𝓝[≠] 0) (𝓝 (coefficient hbar*(r : ℂ))) := by
  have h := (phase_hasDerivAt_zero hbar r).tendsto_slope_zero
  simpa only [phaseSlope,zero_add,phase_zero,Complex.real_smul,Complex.ofReal_inv] using h

theorem phase_sub_one_bound (hbar t r : ℝ) : ‖phase hbar t r-1‖≤‖-t*r/hbar‖ := by
  simpa only [phase,mul_comm] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x:= -t*r/hbar))

theorem phaseSlope_bound (hbar t r : ℝ) : ‖phaseSlope hbar t r‖≤‖r/hbar‖ := by
  by_cases ht : t=0
  · simpa only [phaseSlope,ht,inv_zero,Complex.ofReal_zero,zero_mul,norm_zero] using
      norm_nonneg (r/hbar)
  calc
    ‖phaseSlope hbar t r‖=‖t⁻¹‖*‖phase hbar t r-1‖ := by simp [phaseSlope,norm_mul]
    _ ≤ ‖t⁻¹‖*‖-t*r/hbar‖ := mul_le_mul_of_nonneg_left (phase_sub_one_bound hbar t r) (norm_nonneg _)
    _ = ‖r/hbar‖ := by
      rw [norm_inv,norm_div,norm_mul,norm_neg,← mul_div_assoc,← mul_assoc,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht),one_mul,norm_div]

theorem coefficient_norm (hbar : ℝ) : ‖coefficient hbar‖=‖hbar‖⁻¹ := by
  simp [coefficient,norm_div]

theorem phaseSlope_bound_coefficient (hbar t r : ℝ) :
    ‖phaseSlope hbar t r‖≤‖coefficient hbar‖*‖(r : ℂ)‖ := by
  simpa [coefficient_norm,norm_div,div_eq_mul_inv,mul_comm] using phaseSlope_bound hbar t r

end AASCKleinGordon.Translation
