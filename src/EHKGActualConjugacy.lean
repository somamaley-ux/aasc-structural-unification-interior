import EHKGSecantDynamics
import EHKGConformalCurvature

/-! Actual coordinate-operator conjugacy. This is an operator theorem,
not an assumed Cauchy evolution and not the full source/action attachment. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

theorem time_scalar_partial (A : ℝ → ℝ) (p : CoordinatePoint) (q : ℝ)
    (derivative : HasDerivAt A q (p 0)) (c : Fin 4) :
    scalarPartial (fun x : CoordinatePoint => A (x 0)) p c =
      q * (if c = 0 then 1 else 0) := by
  have first := derivative.comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun x : CoordinatePoint => A (x 0))
    (q • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) p at first
  rw [scalarPartial, first.fderiv]
  simp [Pi.single_apply, eq_comm]

theorem time_scalar_second (A B : ℝ → ℝ) (p : CoordinatePoint) (r : ℝ)
    (nearDerivatives : ∀ᶠ t : ℝ in 𝓝 (p 0), HasDerivAt A (B t) t)
    (second : HasDerivAt B r (p 0)) (c d : Fin 4) :
    scalarSecondPartial (fun x : CoordinatePoint => A (x 0)) p c d =
      r * (if c = 0 then 1 else 0) * (if d = 0 then 1 else 0) := by
  have nearby : ∀ᶠ x : CoordinatePoint in 𝓝 p, HasDerivAt A (B (x 0)) (x 0) :=
    (continuous_apply (0 : Fin 4)).continuousAt.eventually nearDerivatives
  have firstNear : (fun x : CoordinatePoint => scalarPartial (fun y => A (y 0)) x c) =ᶠ[𝓝 p]
      (fun x => B (x 0) * (if c = 0 then 1 else 0)) :=
    nearby.mono (fun x hx => time_scalar_partial A x (B (x 0)) hx c)
  have first := second.comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun x : CoordinatePoint => B (x 0))
    (r • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) p at first
  change fderiv ℝ (fun x => scalarPartial (fun y => A (y 0)) x c) p (Pi.single d 1) = _
  rw [firstNear.fderiv_eq, (first.mul_const (if c = 0 then 1 else 0)).fderiv]
  by_cases hc : c = 0 <;> by_cases hd : d = 0 <;> simp [hc, hd, Pi.single_apply, eq_comm]

theorem secant_time_regular (nu : ℝ) (p : CoordinatePoint) (safe : Real.cos (nu * p 0) ≠ 0) :
    ContDiffAt ℝ 2 (fun x : CoordinatePoint => secantScale nu (x 0)) p := by
  have linear : ContDiff ℝ 2 (fun x : CoordinatePoint => nu * x 0) := by fun_prop
  exact linear.contDiffAt.cos.inv safe

theorem secant_time_partial (nu : ℝ) (p : CoordinatePoint) (safe : Real.cos (nu * p 0) ≠ 0)
    (c : Fin 4) : scalarPartial (fun x : CoordinatePoint => secantScale nu (x 0)) p c =
      secantVelocity nu (p 0) * (if c = 0 then 1 else 0) :=
  time_scalar_partial _ _ _ (secant_scale_hasDerivAt nu (p 0) safe) c

theorem secant_time_second (nu : ℝ) (p : CoordinatePoint) (safe : Real.cos (nu * p 0) ≠ 0)
    (c d : Fin 4) : scalarSecondPartial (fun x : CoordinatePoint => secantScale nu (x 0)) p c d =
      (nu ^ 2 * (2 * secantScale nu (p 0) ^ 3 - secantScale nu (p 0))) *
        (if c = 0 then 1 else 0) * (if d = 0 then 1 else 0) := by
  have nearSafe : ∀ᶠ t : ℝ in 𝓝 (p 0), Real.cos (nu * t) ≠ 0 :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos (nu * t))).continuousAt.eventually_ne safe
  exact time_scalar_second _ _ p _
    (nearSafe.mono (fun t ht => secant_scale_hasDerivAt nu t ht))
    (secant_velocity_hasDerivAt nu (p 0) safe) c d

def flatScalarResidual (massSquared : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  scalarSecondPartial u p 0 0 - scalarSecondPartial u p 1 1 -
    scalarSecondPartial u p 2 2 - scalarSecondPartial u p 3 3 + massSquared * u p

theorem secant_actual_operator_conjugacy (nu : ℝ) (p : CoordinatePoint)
    (safe : Real.cos (nu * p 0) ≠ 0) (u : CoordinatePoint → ℝ) (smooth : ContDiffAt ℝ 2 u p) :
    flatScalarResidual (nu ^ 2) (fun x => secantScale nu (x 0) * u x) p =
      -(secantScale nu (p 0)) ^ 3 *
        (scalarFieldWaveOperator (timeConformalMetric (secantScale nu)) u p -
          (2 * nu ^ 2) * u p) := by
  rw [time_conformal_scalar_wave_operator _ p _ (secant_scale_hasDerivAt nu (p 0) safe)
    (inv_ne_zero safe)]
  simp only [flatScalarResidual, c2_local_scalarSecondPartial_mul _ _ p
    (secant_time_regular nu p safe) smooth, secant_time_partial nu p safe,
    secant_time_second nu p safe]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide,
    if_false, if_true]
  norm_num [Fin.reduceEq]
  have scaleNonzero : secantScale nu (p 0) ≠ 0 := inv_ne_zero safe
  field_simp [scaleNonzero]
  <;> ring

theorem scalar_wave_operator_congr_of_eventuallyEq (g h : MetricField) (p : CoordinatePoint)
    (near : g =ᶠ[𝓝 p] h) (u : CoordinatePoint → ℝ) :
    scalarFieldWaveOperator g u p = scalarFieldWaveOperator h u p := by
  have value : g p = h p := near.eq_of_nhds
  have firstEntries (i j c : Fin 4) : metricPartial g p i j c = metricPartial h p i j c := by
    have entries : (fun x => g x i j) =ᶠ[𝓝 p] (fun x => h x i j) :=
      near.mono (fun x hx => congrArg (fun M : Tensor2 => M i j) hx)
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1)) entries.fderiv_eq
  simp only [scalarFieldWaveOperator, leviCivitaCoefficients, lowerChristoffel, value, firstEntries]

end AASCKleinGordon.CurvedKG
