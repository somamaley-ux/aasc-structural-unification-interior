import EHKGCoordinateCauchy

/-! An actual jointly smooth real field on the original admitted curved operand.
The result is on the protected open chart. Cauchy-domain geometry, local smooth
uniqueness, LF continuity and original-use maps are separate subsequent proofs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap FourierTransform Topology BigOperators
namespace AASCKleinGordon.CurvedKG

def curvedCoordinateField (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (P : ℂ →L[ℝ] ℝ)
    (p : CoordinatePoint) : ℝ :=
  Real.cos (conformalFrequency a * p 0) * flatCoordinateField (auxiliaryKGParameters a) f h P p

theorem curved_coordinate_smooth (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (P : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (curvedCoordinateField a f h P) := by
  have linear : ContDiff ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => conformalFrequency a * p 0) := by fun_prop
  exact linear.cos.mul (flat_coordinate_smooth (auxiliaryKGParameters a) f h P)

theorem protected_rescaled_field (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ)) (P : ℂ →L[ℝ] ℝ)
    (p : CoordinatePoint) (inside : p ∈ protectedConformalBall (conformalFrequency a)) :
    secantScale (conformalFrequency a) (p 0) * curvedCoordinateField a f h P p =
      flatCoordinateField (auxiliaryKGParameters a) f h P p := by
  have safe := ne_of_gt (protected_cosine_positive (conformalFrequency a) p inside)
  dsimp [secantScale, curvedCoordinateField]
  rw [← mul_assoc, inv_mul_cancel₀ safe, one_mul]

theorem flat_residual_congr_of_eventuallyEq (massSquared : ℝ) (F G : CoordinatePoint → ℝ)
    (p : CoordinatePoint) (near : F =ᶠ[𝓝 p] G) :
    flatScalarResidual massSquared F p = flatScalarResidual massSquared G p := by
  have seconds (c d : Fin 4) : scalarSecondPartial F p c d = scalarSecondPartial G p c d := by
    have firstNear : (fun x => scalarPartial F x c) =ᶠ[𝓝 p] (fun x => scalarPartial G x c) :=
      (near.fderiv (𝕜 := ℝ)).mono
        (fun x hx => congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1)) hx)
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single d 1)) firstNear.fderiv_eq
  simp only [flatScalarResidual, seconds, near.eq_of_nhds]

theorem constructed_same_eh_curved_field_equation (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall (conformalFrequency a)) :
    scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a)))
      (curvedCoordinateField a f h P) p =
        (massWaveNumber a) ^ 2 * curvedCoordinateField a f h P p := by
  have smooth : ContDiffAt ℝ 2 (curvedCoordinateField a f h P) p :=
    (curved_coordinate_smooth a f h P).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have conjugacy := protected_same_eh_conjugacy a p inside (curvedCoordinateField a f h P) smooth
  have near : (fun x => secantScale (conformalFrequency a) (x 0) * curvedCoordinateField a f h P x) =ᶠ[𝓝 p]
      flatCoordinateField (auxiliaryKGParameters a) f h P := by
    filter_upwards [(protected_ball_open (conformalFrequency a)).mem_nhds inside] with q hq
    exact protected_rescaled_field a f h P q hq
  rw [flat_residual_congr_of_eventuallyEq _ _ _ p near,
    flat_coordinate_residual_zero] at conjugacy
  have nonzero : secantScale (conformalFrequency a) (p 0) ≠ 0 :=
    inv_ne_zero (ne_of_gt (protected_cosine_positive (conformalFrequency a) p inside))
  exact sub_eq_zero.mp ((mul_eq_zero.mp conjugacy.symm).resolve_left (neg_ne_zero.mpr (pow_ne_zero 3 nonzero)))

theorem constructed_curved_initial_position (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) (initialTime : p 0 = 0) :
    curvedCoordinateField a f h P p = P (f (coordinateSpatialSplit p).2) := by
  simp [curvedCoordinateField, flatCoordinateField, coordinate_split_time, initialTime,
    full_flat_initial_position]

theorem constructed_curved_initial_velocity (a : Parameters) (f h : 𝓢(KGSpatialSpace, ℂ))
    (P : ℂ →L[ℝ] ℝ) (p : CoordinatePoint) (initialTime : p 0 = 0) :
    scalarPartial (curvedCoordinateField a f h P) p 0 = P (h (coordinateSpatialSplit p).2) := by
  have linear : HasFDerivAt (fun x : CoordinatePoint => conformalFrequency a * x 0)
      (conformalFrequency a • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) p :=
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt.const_mul _
  have cosine := (Real.hasDerivAt_cos (conformalFrequency a * p 0)).comp_hasFDerivAt p linear
  have cosineZero : HasFDerivAt (fun x : CoordinatePoint => Real.cos (conformalFrequency a * x 0))
      (0 : CoordinatePoint →L[ℝ] ℝ) p := by
    simpa [initialTime] using cosine
  have fieldDerivative := (flat_coordinate_smooth (auxiliaryKGParameters a) f h P).differentiable (by simp) p
  change fderiv ℝ (fun x => Real.cos (conformalFrequency a * x 0) *
    flatCoordinateField (auxiliaryKGParameters a) f h P x) p (Pi.single 0 1) = _
  have productDerivative := (cosineZero.mul fieldDerivative.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => Real.cos (conformalFrequency a * x 0) *
    flatCoordinateField (auxiliaryKGParameters a) f h P x) p = _ at productDerivative
  rw [productDerivative]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul, initialTime, mul_zero, Real.cos_zero,
    one_mul, add_zero]
  change scalarPartial (flatCoordinateField (auxiliaryKGParameters a) f h P) p 0 = _
  rw [flat_coordinate_time_partial]
  simp [flatCoordinateField, coordinate_split_time, initialTime, full_flat_initial_position]

theorem protected_initial_metric (a : Parameters) (p : CoordinatePoint)
    (inside : p ∈ protectedConformalBall (conformalFrequency a)) (initialTime : p 0 = 0) :
    originalEHActMetric (conformalOperand (conformalFrequency a)) p = metric := by
  rw [protected_metric_identity _ p inside]
  simp [timeConformalMetric, secantScale, initialTime]

end AASCKleinGordon.CurvedKG
