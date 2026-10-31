import Mathlib.Analysis.Calculus.MeanValue

/-! A scalar Taylor estimate from actual derivatives. The error conclusion is
not an input; later modules construct derivative bounds from compactness. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set
namespace AASCKleinGordon.RecoveryComparison

theorem zero_jet_second_order_bound (F G H : ℝ → ℝ) (r C : ℝ)
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (first : ∀ t, HasDerivAt F (G t) t)
    (second : ∀ t, HasDerivAt G (H t) t)
    (bound : ∀ t, |t| ≤ r → |H t| ≤ C) (valueZero : F 0 = 0) (jetZero : G 0 = 0)
    (t : ℝ) (inside : |t| ≤ r) : |G t| ≤ C*|t| ∧ |F t| ≤ C*t^2 := by
  have jet (s : ℝ) (hs : |s| ≤ r) : |G s| ≤ C*|s| := by
    have estimate := (convex_Icc (-r) r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (second x).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using bound x (abs_le.mpr hx))
      (show (0:ℝ) ∈ Icc (-r) r from ⟨by linarith,hr⟩) (abs_le.mp hs)
    simpa only [jetZero,sub_zero,Real.norm_eq_abs] using estimate
  refine ⟨jet t inside,?_⟩
  have estimate := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (first x).hasDerivWithinAt)
    (fun x hx => by
      have hxt : |x| ≤ |t| := abs_le.mpr hx
      exact (show ‖G x‖ ≤ C*|x| by simpa only [Real.norm_eq_abs] using jet x (hxt.trans inside)).trans
        (mul_le_mul_of_nonneg_left hxt hC))
    (show (0:ℝ) ∈ Icc (-|t|) |t| from ⟨neg_nonpos.mpr (abs_nonneg t),abs_nonneg t⟩)
    (show t ∈ Icc (-|t|) |t| from ⟨neg_abs_le t,le_abs_self t⟩)
  simpa only [valueZero,sub_zero,Real.norm_eq_abs,mul_assoc,←pow_two,sq_abs] using estimate

end AASCKleinGordon.RecoveryComparison
