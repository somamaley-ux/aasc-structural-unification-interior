import KGEnergyTemperate
import Mathlib.Analysis.Complex.Trigonometric

noncomputable section
namespace AASCKleinGordon

def axisBoostFour (r : ℝ) (q : FourMomentum) : FourMomentum :=
  ![Real.cosh r*q 0 + Real.sinh r*q 1,
    Real.sinh r*q 0 + Real.cosh r*q 1, q 2, q 3]

theorem axisBoostFour_zero (q : FourMomentum) : axisBoostFour 0 q = q := by
  ext i
  fin_cases i <;> simp [axisBoostFour]

theorem axisBoostFour_add (r s : ℝ) (q : FourMomentum) :
    axisBoostFour (r+s) q = axisBoostFour r (axisBoostFour s q) := by
  ext i
  fin_cases i <;> simp [axisBoostFour, Real.cosh_add, Real.sinh_add] <;> ring

theorem axisBoostFour_neg_inverse (r : ℝ) (q : FourMomentum) :
    axisBoostFour (-r) (axisBoostFour r q) = q := by
  rw [← axisBoostFour_add, neg_add_cancel, axisBoostFour_zero]

def axisBoostFourCLE (r : ℝ) : FourMomentum ≃L[ℝ] FourMomentum :=
  ({ toFun := axisBoostFour r
     invFun := axisBoostFour (-r)
     left_inv := axisBoostFour_neg_inverse r
     right_inv := by intro q; simpa only [neg_neg] using axisBoostFour_neg_inverse (-r) q
     map_add' := by
       intro q t
       ext i
       fin_cases i <;> simp [axisBoostFour] <;> ring
     map_smul' := by
       intro c q
       ext i
       fin_cases i <;> simp [axisBoostFour] <;> ring } :
    FourMomentum ≃ₗ[ℝ] FourMomentum).toContinuousLinearEquiv

theorem axisBoostFour_preserves_minkowski (r : ℝ) (q t : FourMomentum) :
    minkowskiDot (axisBoostFour r q) (axisBoostFour r t) = minkowskiDot q t := by
  change -((Real.cosh r*q 0 + Real.sinh r*q 1)*(Real.cosh r*t 0 + Real.sinh r*t 1)) +
    (Real.sinh r*q 0 + Real.cosh r*q 1)*(Real.sinh r*t 0 + Real.cosh r*t 1) +
    q 2*t 2 + q 3*t 3 = _
  calc
    _ = -(Real.cosh r^2-Real.sinh r^2)*(q 0*t 0) +
        (Real.cosh r^2-Real.sinh r^2)*(q 1*t 1) + q 2*t 2 + q 3*t 3 := by ring
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; dsimp [minkowskiDot]; ring

theorem energy_div_speed_gt_abs_first (a : Parameters) (p : Momentum) :
    |p 0| < energy a p/a.speed := by
  have hs := massShell_on_shell a p
  change -(energy a p/a.speed*(energy a p/a.speed)) + p 0*p 0 + p 1*p 1 + p 2*p 2 =
    -(a.mass^2*a.speed^2) at hs
  have hm : 0 < a.mass^2*a.speed^2 := mul_pos (sq_pos_of_pos a.mass_pos) (sq_pos_of_pos a.speed_pos)
  have he : 0 < energy a p/a.speed := div_pos (energy_pos a p) a.speed_pos
  apply (sq_lt_sq₀ (abs_nonneg (p 0)) he.le).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]

theorem abs_sinh_le_cosh (r : ℝ) : |Real.sinh r| ≤ Real.cosh r := by
  apply abs_le.mpr
  constructor
  · have h := Real.sinh_lt_cosh (x := -r)
    simp only [Real.sinh_neg, Real.cosh_neg] at h
    linarith
  · exact (Real.sinh_lt_cosh (x := r)).le

def axisBoostTime (a : Parameters) (r : ℝ) (p : Momentum) : ℝ :=
  Real.cosh r*(energy a p/a.speed) + Real.sinh r*p 0

def axisBoostMomentum (a : Parameters) (r : ℝ) (p : Momentum) : Momentum :=
  ![Real.sinh r*(energy a p/a.speed) + Real.cosh r*p 0, p 1, p 2]

theorem axisBoostTime_pos (a : Parameters) (r : ℝ) (p : Momentum) :
    0 < axisBoostTime a r p := by
  have hb : |Real.sinh r*p 0| < Real.cosh r*(energy a p/a.speed) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (abs_sinh_le_cosh r) (abs_nonneg _)).trans_lt
      (mul_lt_mul_of_pos_left (energy_div_speed_gt_abs_first a p) (Real.cosh_pos r))
  have hl := neg_abs_le (Real.sinh r*p 0)
  dsimp [axisBoostTime]
  linarith

theorem axisBoostMomentum_energy (a : Parameters) (r : ℝ) (p : Momentum) :
    energy a (axisBoostMomentum a r p)/a.speed = axisBoostTime a r p := by
  have hpres := axisBoostFour_preserves_minkowski r (massShell a p) (massShell a p)
  rw [massShell_on_shell] at hpres
  change -(axisBoostTime a r p*axisBoostTime a r p) +
      axisBoostMomentum a r p 0*axisBoostMomentum a r p 0 +
      axisBoostMomentum a r p 1*axisBoostMomentum a r p 1 +
      axisBoostMomentum a r p 2*axisBoostMomentum a r p 2 = -(a.mass^2*a.speed^2) at hpres
  have hs := massShell_on_shell a (axisBoostMomentum a r p)
  change -(energy a (axisBoostMomentum a r p)/a.speed*(energy a (axisBoostMomentum a r p)/a.speed)) +
    axisBoostMomentum a r p 0*axisBoostMomentum a r p 0 +
    axisBoostMomentum a r p 1*axisBoostMomentum a r p 1 +
    axisBoostMomentum a r p 2*axisBoostMomentum a r p 2 = -(a.mass^2*a.speed^2) at hs
  have he := div_pos (energy_pos a (axisBoostMomentum a r p)) a.speed_pos
  have ht := axisBoostTime_pos a r p
  nlinarith

theorem massShell_axisBoost (a : Parameters) (r : ℝ) (p : Momentum) :
    massShell a (axisBoostMomentum a r p) = axisBoostFour r (massShell a p) := by
  ext i
  fin_cases i
  · exact axisBoostMomentum_energy a r p
  all_goals rfl

theorem axisBoostMomentum_add (a : Parameters) (r s : ℝ) (p : Momentum) :
    axisBoostMomentum a (r+s) p = axisBoostMomentum a r (axisBoostMomentum a s p) := by
  have h := axisBoostFour_add r s (massShell a p)
  rw [← massShell_axisBoost, ← massShell_axisBoost, ← massShell_axisBoost] at h
  ext i
  have hi := congrArg (fun q : FourMomentum => q i.succ) h
  exact hi

theorem axisBoostMomentum_zero (a : Parameters) (p : Momentum) :
    axisBoostMomentum a 0 p = p := by
  ext i
  fin_cases i <;> simp [axisBoostMomentum]

theorem axisBoostMomentum_neg_inverse (a : Parameters) (r : ℝ) (p : Momentum) :
    axisBoostMomentum a (-r) (axisBoostMomentum a r p) = p := by
  rw [← axisBoostMomentum_add, neg_add_cancel, axisBoostMomentum_zero]

end AASCKleinGordon
