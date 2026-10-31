import EHKGActualScalarDensity

/-! Pointwise identification of the actual scalar action densities, including
the actual time-divergence term. An integrated boundary statement must retain
its domain/integrability or compact-variation conditions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def secantLogVelocity (nu t : ℝ) : ℝ := secantVelocity nu t / secantScale nu t

def secantBoundaryFlux (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  secantLogVelocity nu (p 0) * (secantLift nu u p) ^ 2

theorem secant_lift_partial (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (safe : Real.cos (nu * p 0) ≠ 0) (regular : ContDiffAt ℝ 2 u p) (c : Fin 4) :
    scalarPartial (secantLift nu u) p c =
      secantScale nu (p 0) * scalarPartial u p c +
        u p * secantVelocity nu (p 0) * (if c = 0 then 1 else 0) := by
  change scalarPartial (fun x => secantScale nu (x 0) * u x) p c = _
  rw [c2_local_scalarPartial_mul _ _ p (secant_time_regular nu p safe) regular,
    secant_time_partial nu p safe]
  ring

theorem secant_boundary_time_partial (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (safe : Real.cos (nu * p 0) ≠ 0) (regular : ContDiffAt ℝ 2 u p) :
    scalarPartial (secantBoundaryFlux nu u) p 0 =
      ((nu ^ 2 * (2 * secantScale nu (p 0) ^ 3 - secantScale nu (p 0)) *
          secantScale nu (p 0) - secantVelocity nu (p 0) ^ 2) / secantScale nu (p 0) ^ 2) *
        (secantScale nu (p 0) * u p) ^ 2 +
      (secantVelocity nu (p 0) / secantScale nu (p 0)) *
        2 * (secantScale nu (p 0) * u p) *
          (secantScale nu (p 0) * scalarPartial u p 0 + secantVelocity nu (p 0) * u p) := by
  have scaleD := (secant_scale_hasDerivAt nu (p 0) safe).comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  have logD := ((secant_velocity_hasDerivAt nu (p 0) safe).div
    (secant_scale_hasDerivAt nu (p 0) safe) (inv_ne_zero safe)).comp_hasFDerivAt p
      (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  have fieldD := scaleD.mul (regular.differentiableAt (by norm_num)).hasFDerivAt
  have boundaryD := logD.mul (fieldD.pow 2)
  change fderiv ℝ (fun x => (secantVelocity nu (x 0) / secantScale nu (x 0)) *
    (secantScale nu (x 0) * u x) ^ 2) p (Pi.single 0 1) = _
  have actualD := boundaryD.fderiv
  change fderiv ℝ (fun x => (secantVelocity nu (x 0) / secantScale nu (x 0)) *
    (secantScale nu (x 0) * u x) ^ 2) p = _ at actualD
  rw [actualD]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_eq_same, smul_eq_mul,
    Function.comp_def, Pi.mul_apply, Pi.div_apply, Nat.reduceSub, pow_one]
  change _ = _
  dsimp only [scalarPartial]
  ring

theorem rescaled_density_boundary_algebra (A q nu u u0 u1 u2 u3 : ℝ) (nonzero : A ≠ 0) :
    (1 / 2 : ℝ) * (A ^ 2 * (u0 ^ 2 - u1 ^ 2 - u2 ^ 2 - u3 ^ 2) - 2 * nu ^ 2 * A ^ 4 * u ^ 2) =
      (1 / 2 : ℝ) * ((A * u0 + q * u) ^ 2 - (A * u1) ^ 2 - (A * u2) ^ 2 -
        (A * u3) ^ 2 - nu ^ 2 * (A * u) ^ 2) -
      (1 / 2 : ℝ) * (((nu ^ 2 * (2 * A ^ 3 - A) * A - q ^ 2) / A ^ 2) * (A * u) ^ 2 +
        (q / A) * 2 * (A * u) * (A * u0 + q * u)) := by
  field_simp [nonzero]
  <;> ring

theorem protected_same_eh_action_density_boundary (a : Parameters)
    (u : CoordinatePoint → ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond (conformalFrequency a)) (regular : ContDiffAt ℝ 2 u p) :
    sameEHScalarDensity a u p =
      nativeRealClockDensity metric (scalarPartial (secantLift (conformalFrequency a) u) p)
        (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2) -
      (1 / 2 : ℝ) * scalarPartial (secantBoundaryFlux (conformalFrequency a) u) p 0 := by
  have safe : Real.cos (conformalFrequency a * p 0) ≠ 0 :=
    ne_of_gt (protected_cosine_positive _ _ (protected_diamond_subset_ball _ inside))
  have flatDensity := time_conformal_scalar_density (fun _ : ℝ => 1) p (by norm_num)
    (scalarPartial (secantLift (conformalFrequency a) u) p)
    (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2)
  have flatMetric : timeConformalMetric (fun _ : ℝ => 1) p = metric := by
    simp [timeConformalMetric]
  rw [flatMetric] at flatDensity
  rw [protected_same_eh_scalar_density a u p inside, flatDensity,
    secant_boundary_time_partial _ u p safe regular, conformal_frequency_mass]
  simp only [one_pow, one_mul, secant_lift_partial _ u p safe regular,
    show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, if_false, if_true, mul_one, mul_zero, add_zero, secantLift]
  convert rescaled_density_boundary_algebra (secantScale (conformalFrequency a) (p 0))
    (secantVelocity (conformalFrequency a) (p 0)) (conformalFrequency a) (u p)
    (scalarPartial u p 0) (scalarPartial u p 1) (scalarPartial u p 2) (scalarPartial u p 3)
    (inv_ne_zero safe) using 1 <;> ring

end AASCKleinGordon.CurvedKG
