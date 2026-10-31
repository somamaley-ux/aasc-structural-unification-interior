import EHKGTimeAffineCalculus
import EHKGCoordinateFoliation

/-! Fourier reinitialization at an actual noncentral time on the same
admitted EH operand. Input data are the conjugated field and time derivative;
the physical field and geometric-normal traces are derived explicitly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG

def shiftedFlatSchwartzField (a : Parameters) (time : ℝ)
    (f h : 𝓢(KGSpatialSpace, ℂ)) (p : CoordinatePoint) : ℝ :=
  flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM (timeAffineMap (-time) 1 p)

def shiftedCurvedSchwartzField (a : Parameters) (time : ℝ)
    (f h : 𝓢(KGSpatialSpace, ℂ)) (p : CoordinatePoint) : ℝ :=
  Real.cos (conformalFrequency a * p 0) * shiftedFlatSchwartzField a time f h p

theorem shifted_flat_smooth (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (shiftedFlatSchwartzField a time f h) :=
  (flat_coordinate_smooth _ _ _ _).comp (time_affine_smooth _ _)

theorem shifted_curved_smooth (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (shiftedCurvedSchwartzField a time f h) := by
  have cosine : ContDiff ℝ (⊤ : ℕ∞) (fun p : CoordinatePoint => Real.cos (conformalFrequency a * p 0)) := by fun_prop
  exact cosine.mul (shifted_flat_smooth a time f h)

theorem shifted_flat_equation (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ))
    (p : CoordinatePoint) :
    flatScalarResidual ((massWaveNumber (auxiliaryKGParameters a)) ^ 2)
      (shiftedFlatSchwartzField a time f h) p = 0 := by
  have atF := (flat_coordinate_smooth (auxiliaryKGParameters a) f h Complex.reCLM).contDiffAt
    (x := timeAffineMap (-time) 1 p)
  have equation := flat_residual_time_affine (-time) 1 (massWaveNumber (auxiliaryKGParameters a))
    (flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM) p
    (atF.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  simpa only [one_mul, one_pow, flat_coordinate_residual_zero] using equation

theorem shifted_curved_same_eh_equation (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ))
    (p : CoordinatePoint) (inside : p ∈ protectedConformalBall (conformalFrequency a)) :
    scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a)))
      (shiftedCurvedSchwartzField a time f h) p =
        (massWaveNumber a) ^ 2 * shiftedCurvedSchwartzField a time f h p := by
  have smooth := (shifted_curved_smooth a time f h).contDiffAt (x := p)
  have conjugacy := protected_same_eh_conjugacy a p inside (shiftedCurvedSchwartzField a time f h)
    (smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  have near : (fun q => secantScale (conformalFrequency a) (q 0) * shiftedCurvedSchwartzField a time f h q) =ᶠ[𝓝 p]
      shiftedFlatSchwartzField a time f h := by
    filter_upwards [(protected_ball_open _).mem_nhds inside] with q hq
    have safe := ne_of_gt (protected_cosine_positive _ q hq)
    dsimp [secantScale, shiftedCurvedSchwartzField]
    rw [← mul_assoc, inv_mul_cancel₀ safe, one_mul]
  rw [flat_residual_congr_of_eventuallyEq _ _ _ p near, shifted_flat_equation] at conjugacy
  have nonzero : secantScale (conformalFrequency a) (p 0) ≠ 0 :=
    inv_ne_zero (ne_of_gt (protected_cosine_positive _ p inside))
  exact sub_eq_zero.mp ((mul_eq_zero.mp conjugacy.symm).resolve_left (neg_ne_zero.mpr (pow_ne_zero 3 nonzero)))

theorem shifted_slice_time_zero (time : ℝ) (x : KGSpatialSpace) :
    timeAffineMap (-time) 1 (evolutionSlicePoint time x) 0 = 0 := by
  change -time * (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) 0 + 1 * evolutionSlicePoint time x 0 = 0
  simp [evolution_slice_time]

theorem shifted_slice_space (time : ℝ) (x : KGSpatialSpace) :
    (coordinateSpatialSplit (timeAffineMap (-time) 1 (evolutionSlicePoint time x))).2 = x := by
  rw [coordinate_split_space]
  have tail : Fin.tail (timeAffineMap (-time) 1 (evolutionSlicePoint time x)) = Fin.tail (evolutionSlicePoint time x) := by
    funext i
    change -time * (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) i.succ + 1 * evolutionSlicePoint time x i.succ = _
    simp [Fin.tail]
  rw [tail, ← coordinate_split_space, evolution_slice_space]

theorem shifted_flat_position (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ))
    (x : KGSpatialSpace) : shiftedFlatSchwartzField a time f h (evolutionSlicePoint time x) = (f x).re := by
  simp only [shiftedFlatSchwartzField, flatCoordinateField, coordinate_split_time, shifted_slice_time_zero,
    full_flat_initial_position, shifted_slice_space]
  rfl

theorem shifted_flat_velocity (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ))
    (x : KGSpatialSpace) : scalarPartial (shiftedFlatSchwartzField a time f h) (evolutionSlicePoint time x) 0 = (h x).re := by
  have atF := (flat_coordinate_smooth (auxiliaryKGParameters a) f h Complex.reCLM).differentiable (by simp)
    (timeAffineMap (-time) 1 (evolutionSlicePoint time x))
  change scalarPartial (fun p => flatCoordinateField (auxiliaryKGParameters a) f h Complex.reCLM
    (timeAffineMap (-time) 1 p)) (evolutionSlicePoint time x) 0 = _
  rw [scalar_partial_time_affine (-time) 1 _ _ atF, one_mul, flat_coordinate_time_partial]
  simp only [flatCoordinateField, coordinate_split_time, shifted_slice_time_zero,
    full_flat_initial_position, shifted_slice_space]
  rfl

theorem shifted_curved_position (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ))
    (x : KGSpatialSpace) : shiftedCurvedSchwartzField a time f h (evolutionSlicePoint time x) =
      Real.cos (conformalFrequency a * time) * (f x).re := by
  rw [shiftedCurvedSchwartzField, evolution_slice_time, shifted_flat_position]

theorem normal_derivative_is_cosine_partial (nu : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint) :
    actualNormalDerivative nu u p = Real.cos (nu * p 0) * scalarPartial u p 0 := by
  change fderiv ℝ u p (Real.cos (nu * p 0) • (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint)) = _
  rw [map_smul]
  rfl

theorem shifted_curved_normal (a : Parameters) (time : ℝ) (f h : 𝓢(KGSpatialSpace, ℂ))
    (x : KGSpatialSpace) :
    actualNormalDerivative (conformalFrequency a) (shiftedCurvedSchwartzField a time f h) (evolutionSlicePoint time x) =
      Real.cos (conformalFrequency a * time) *
        (-(conformalFrequency a) * Real.sin (conformalFrequency a * time) * (f x).re +
          Real.cos (conformalFrequency a * time) * (h x).re) := by
  let p := evolutionSlicePoint time x
  have phase : HasFDerivAt (fun q : CoordinatePoint => conformalFrequency a * q 0)
      (conformalFrequency a • (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ)) p :=
    (ContinuousLinearMap.proj (0 : Fin 4) : CoordinatePoint →L[ℝ] ℝ).hasFDerivAt.const_mul (conformalFrequency a)
  have cosine := (Real.hasDerivAt_cos (conformalFrequency a * p 0)).comp_hasFDerivAt p phase
  have productDerivative := (cosine.mul ((shifted_flat_smooth a time f h).differentiable (by simp) p).hasFDerivAt).fderiv
  change fderiv ℝ (fun q => Real.cos (conformalFrequency a * q 0) * shiftedFlatSchwartzField a time f h q) p = _
    at productDerivative
  rw [normal_derivative_is_cosine_partial, evolution_slice_time]
  change Real.cos (conformalFrequency a * time) *
    fderiv ℝ (fun q => Real.cos (conformalFrequency a * q 0) * shiftedFlatSchwartzField a time f h q) p (Pi.single 0 1) = _
  rw [productDerivative]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Function.comp_apply]
  change Real.cos (conformalFrequency a * time) *
    (Real.cos (conformalFrequency a * p 0) * scalarPartial (shiftedFlatSchwartzField a time f h) p 0 +
      shiftedFlatSchwartzField a time f h p * (-Real.sin (conformalFrequency a * p 0) * (conformalFrequency a * 1))) = _
  dsimp only [p]
  rw [evolution_slice_time, shifted_flat_position, shifted_flat_velocity]
  ring

end AASCKleinGordon.CurvedKG
