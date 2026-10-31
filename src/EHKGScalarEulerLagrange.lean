import EHKGCompactFluxIntegral

/-! The actual field-variation density equals the actual compact flux
divergence plus the same-metric KG residual. Neither the Euler-Lagrange
operator nor its identification with the PDE is received as a certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def scalarFieldVariationDensity (a : Parameters) (u d : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  sameEHScalarDensity a (fun q => u q + d q) p - sameEHScalarDensity a u p - sameEHScalarDensity a d p

theorem protected_conformal_factor (nu : ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedDiamond nu) : conformalMetricFactor nu p = secantScale nu (p 0) ^ 2 := by
  have matrices := (conformal_operand_actual_metric nu p).symm.trans
    (protected_metric_identity nu p (protected_diamond_subset_ball nu inside))
  have entry := congrArg (fun M : Tensor2 => M 1 1) matrices
  change conformalMetricFactor nu p * 1 = secantScale nu (p 0) ^ 2 * 1 at entry
  simpa using entry

theorem protected_variation_density (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) :
    scalarFieldVariationDensity a u d p =
      secantScale (conformalFrequency a) (p 0) ^ 2 *
        (scalarPartial u p 0 * scalarPartial d p 0 - scalarPartial u p 1 * scalarPartial d p 1 -
          scalarPartial u p 2 * scalarPartial d p 2 - scalarPartial u p 3 * scalarPartial d p 3) -
      (massWaveNumber a) ^ 2 * secantScale (conformalFrequency a) (p 0) ^ 4 * u p * d p := by
  have sumFirst (i : Fin 4) : scalarPartial (fun q => u q + d q) p i =
      scalarPartial u p i + scalarPartial d p i := by
    simpa using scalar_partial_add_real_multiple u d regularU regularD 1 p i
  rw [scalarFieldVariationDensity, protected_same_eh_scalar_density a _ p inside,
    protected_same_eh_scalar_density a u p inside, protected_same_eh_scalar_density a d p inside]
  simp only [sumFirst]
  ring

def timeScalarVariationFlux (nu : ℝ) (u d : CoordinatePoint → ℝ) (i : Fin 4)
    (p : CoordinatePoint) : ℝ :=
  ((if i = 0 then 1 else -1) * secantScale nu (p 0) ^ 2 * scalarPartial u p i) * d p

theorem time_scalar_variation_flux_partial (nu : ℝ) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (p : CoordinatePoint) (safe : Real.cos (nu * p 0) ≠ 0) (i : Fin 4) :
    scalarPartial (timeScalarVariationFlux nu u d i) p i =
      (if i = 0 then 1 else -1) *
        (2 * secantScale nu (p 0) * secantVelocity nu (p 0) * (if i = 0 then 1 else 0) *
          scalarPartial u p i * d p +
        secantScale nu (p 0) ^ 2 * scalarSecondPartial u p i i * d p +
        secantScale nu (p 0) ^ 2 * scalarPartial u p i * scalarPartial d p i) := by
  have factorD := ((secant_scale_hasDerivAt nu (p 0) safe).pow 2).comp_hasFDerivAt p
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt
  have uD := (scalar_partial_smooth u regularU i).differentiable (by simp) p
  have dD := regularD.differentiable (by simp) p
  have fluxD := (((factorD.const_mul (if i = 0 then 1 else -1)).mul uD.hasFDerivAt).mul dD.hasFDerivAt).fderiv
  change fderiv ℝ (fun q => ((if i = 0 then 1 else -1) * secantScale nu (q 0) ^ 2 *
    scalarPartial u q i) * d q) p = _ at fluxD
  change fderiv ℝ (fun q => ((if i = 0 then 1 else -1) * secantScale nu (q 0) ^ 2 *
    scalarPartial u q i) * d q) p (Pi.single i 1) = _
  rw [fluxD]
  dsimp only [scalarPartial, scalarSecondPartial]
  by_cases hi : i = 0 <;>
    simp [hi, Function.comp_def, Pi.single_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, eq_comm] <;> ring

theorem actual_scalar_variation_flux_partial_on_diamond (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) (i : Fin 4) :
    scalarPartial (actualScalarVariationFlux a u d i) p i =
      scalarPartial (timeScalarVariationFlux (conformalFrequency a) u d i) p i := by
  have near : actualScalarVariationFlux a u d i =ᶠ[𝓝 p]
      timeScalarVariationFlux (conformalFrequency a) u d i := by
    filter_upwards [(protected_diamond_open _).mem_nhds inside] with q hq
    simp only [actualScalarVariationFlux, timeScalarVariationFlux, protected_conformal_factor _ q hq]
  exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single i 1)) near.fderiv_eq

theorem same_eh_scalar_euler_lagrange_identity (a : Parameters) (u d : CoordinatePoint → ℝ)
    (regularU : ContDiff ℝ (⊤ : ℕ∞) u) (regularD : ContDiff ℝ (⊤ : ℕ∞) d)
    (p : CoordinatePoint) (inside : p ∈ protectedDiamond (conformalFrequency a)) :
    scalarFieldVariationDensity a u d p = actualScalarVariationDivergence a u d p +
      secantScale (conformalFrequency a) (p 0) ^ 4 *
        (scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p -
          (massWaveNumber a) ^ 2 * u p) * d p := by
  have safe := ne_of_gt (protected_cosine_positive _ _ (protected_diamond_subset_ball _ inside))
  rw [protected_variation_density a u d regularU regularD p inside,
    protected_operator_identity _ p (protected_diamond_subset_ball _ inside),
    time_conformal_scalar_wave_operator _ p _ (secant_scale_hasDerivAt _ _ safe) (inv_ne_zero safe)]
  simp only [actualScalarVariationDivergence,
    actual_scalar_variation_flux_partial_on_diamond a u d regularU regularD p inside,
    Fin.sum_univ_four, time_scalar_variation_flux_partial _ u d regularU regularD p safe,
    show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, if_false, if_true, mul_one, one_mul, mul_zero, zero_mul, zero_add]
  have scaleNonzero : secantScale (conformalFrequency a) (p 0) ≠ 0 := inv_ne_zero safe
  field_simp [scaleNonzero]
  <;> ring

end AASCKleinGordon.CurvedKG
