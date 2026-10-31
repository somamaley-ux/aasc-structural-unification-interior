import EHKGConformalOperator
import KGMassShell
import KGSchwartzDifferential

/-! Exact analytic conformal scale and physical/auxiliary mass bookkeeping.
These derivatives are proved from trigonometry; no scale ODE is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def secantScale (nu t : ℝ) : ℝ := (Real.cos (nu * t))⁻¹

def secantVelocity (nu t : ℝ) : ℝ := nu * Real.sin (nu * t) * secantScale nu t ^ 2

theorem secant_scale_hasDerivAt (nu t : ℝ) (safe : Real.cos (nu * t) ≠ 0) :
    HasDerivAt (secantScale nu) (secantVelocity nu t) t := by
  have cosine := (Real.hasDerivAt_cos (nu * t)).comp t ((hasDerivAt_id t).const_mul nu)
  convert cosine.inv safe using 1
  dsimp [secantScale, secantVelocity]
  field_simp
  <;> ring

theorem secant_velocity_hasDerivAt (nu t : ℝ) (safe : Real.cos (nu * t) ≠ 0) :
    HasDerivAt (secantVelocity nu)
      (nu ^ 2 * (2 * secantScale nu t ^ 3 - secantScale nu t)) t := by
  have sine := (Real.hasDerivAt_sin (nu * t)).comp t ((hasDerivAt_id t).const_mul nu)
  have scale := secant_scale_hasDerivAt nu t safe
  convert (sine.const_mul nu).mul (scale.pow 2) using 1
  dsimp [secantScale, secantVelocity]
  field_simp
  have trig := Real.sin_sq_add_cos_sq (nu * t)
  nlinarith [sq_nonneg nu]

theorem secant_scale_zero (nu : ℝ) : secantScale nu 0 = 1 := by simp [secantScale]

theorem secant_velocity_zero (nu : ℝ) : secantVelocity nu 0 = 0 := by simp [secantVelocity]

theorem secant_scale_positive (nu t : ℝ) (positiveCosine : 0 < Real.cos (nu * t)) :
    0 < secantScale nu t := inv_pos.mpr positiveCosine

theorem secant_effective_mass (mu2 nu t : ℝ) (safe : Real.cos (nu * t) ≠ 0)
    (mass : mu2 = 2 * nu ^ 2) :
    mu2 * secantScale nu t ^ 2 -
      (nu ^ 2 * (2 * secantScale nu t ^ 3 - secantScale nu t)) / secantScale nu t = nu ^ 2 := by
  have nonzero : secantScale nu t ≠ 0 := inv_ne_zero safe
  rw [mass]
  field_simp
  <;> ring

def conformalFrequency (a : Parameters) : ℝ := massWaveNumber a / Real.sqrt 2

theorem conformal_frequency_positive (a : Parameters) : 0 < conformalFrequency a := by
  unfold conformalFrequency massWaveNumber
  exact div_pos (div_pos (mul_pos a.mass_pos a.speed_pos) a.hbar_pos) (Real.sqrt_pos.mpr (by norm_num))

theorem conformal_frequency_mass (a : Parameters) :
    (massWaveNumber a) ^ 2 = 2 * conformalFrequency a ^ 2 := by
  have rootSquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  dsimp [conformalFrequency]
  rw [div_pow, rootSquare]
  ring

end AASCKleinGordon.CurvedKG
