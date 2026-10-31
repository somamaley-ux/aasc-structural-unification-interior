import RCInitialSourceComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Quantitative estimates for the actual protected conformal metric.
Constants are explicit; no asymptotic or normal-coordinate bridge is supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology
namespace AASCKleinGordon.RecoveryComparison

theorem cosine_quadratic_error (x : ℝ) (hx : |x| ≤ 1) : |Real.cos x-1| ≤ x^2 := by
  have estimate := zero_jet_second_order_bound (fun s => Real.cos s-1)
    (fun s => -Real.sin s) (fun s => -Real.cos s) 1 1 (by norm_num) (by norm_num)
    (fun s => (Real.hasDerivAt_cos s).sub_const 1)
    (fun s => (Real.hasDerivAt_sin s).neg)
    (fun s _ => by simpa only [abs_neg] using Real.abs_cos_le_one s)
    (by norm_num) (by norm_num) x hx
  simpa only [one_mul] using estimate.2

theorem secant_quadratic_bounds (x : ℝ) (hx : |x| ≤ (1:ℝ)/2) :
    0 ≤ (Real.cos x)⁻¹-1 ∧ (Real.cos x)⁻¹-1 ≤ 2*x^2 ∧
      0 ≤ (Real.cos x)⁻¹^2-1 ∧ (Real.cos x)⁻¹^2-1 ≤ 6*x^2 := by
  have cosine := cosine_quadratic_error x (hx.trans (by norm_num))
  have square : x^2 ≤ (1:ℝ)/4 := by nlinarith [sq_abs x,abs_nonneg x]
  have cosineLower : (1:ℝ)/2 ≤ Real.cos x := by
    have side := neg_le_abs (Real.cos x-1)
    linarith
  have cosinePositive : 0 < Real.cos x := by linarith
  have inversePositive : 0 ≤ (Real.cos x)⁻¹ := inv_nonneg.mpr cosinePositive.le
  have cancel := mul_inv_cancel₀ cosinePositive.ne'
  have inverseUpper : (Real.cos x)⁻¹ ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right cosineLower inversePositive]
  have inverseLower : 1 ≤ (Real.cos x)⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_right (Real.cos_le_one x) inversePositive]
  have numerator : 1-Real.cos x ≤ x^2 := by linarith [neg_le_abs (Real.cos x-1)]
  have identity : (Real.cos x)⁻¹-1 = (1-Real.cos x)*(Real.cos x)⁻¹ := by
    rw [sub_mul,one_mul,cancel]
  have error : (Real.cos x)⁻¹-1 ≤ 2*x^2 := by
    rw [identity]
    exact (mul_le_mul_of_nonneg_right numerator inversePositive).trans
      (by nlinarith [mul_le_mul_of_nonneg_left inverseUpper (sq_nonneg x)])
  refine ⟨by linarith,error,by nlinarith,?_⟩
  have product := mul_le_mul_of_nonneg_right error (show 0 ≤ (Real.cos x)⁻¹+1 by positivity)
  have upper := mul_le_mul_of_nonneg_left (show (Real.cos x)⁻¹+1 ≤ 3 by linarith) (show 0 ≤ 2*x^2 by positivity)
  nlinarith [product,upper]

theorem protected_lapse_exact (a : Parameters) (p : CoordinatePoint) (inside : p ∈ sourceDomain a) :
    scalarSourceLapse a p = secantScale (conformalFrequency a) (p 0) := by
  rw [scalarSourceLapse,source_factor_protected a p inside,Real.sqrt_sq_eq_abs,
    abs_of_pos (secant_scale_positive _ _
      (protected_cosine_positive _ p (protected_diamond_subset_ball _ inside)))]

theorem protected_scale_error_bounds (a : Parameters) (p : CoordinatePoint)
    (inside : p ∈ sourceDomain a) (small : |conformalFrequency a*p 0| ≤ (1:ℝ)/2) :
    |scalarSourceLapse a p-1| ≤ 2*(conformalFrequency a*p 0)^2 ∧
      |sourceFactor a p-1| ≤ 6*(conformalFrequency a*p 0)^2 := by
  have estimates := secant_quadratic_bounds (conformalFrequency a*p 0) small
  rw [protected_lapse_exact a p inside,source_factor_protected a p inside]
  simp only [secantScale]
  constructor
  · rw [abs_of_nonneg estimates.1]
    exact estimates.2.1
  · rw [abs_of_nonneg estimates.2.2.1]
    exact estimates.2.2.2

end AASCKleinGordon.RecoveryComparison
