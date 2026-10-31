import RCDilationDomain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Actual proper-duration rates for the fixed conformal metric and scaled paths.
The small-scale comparison is not a fixed-mass rescaled field equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology BigOperators Interval
namespace AASCKleinGordon.RecoveryComparison

def durationRate (a : Parameters) (M : Tensor2) (v : CoordinatePoint) : ℝ :=
  Real.sqrt (-wickMatrixQuadratic M v)/a.speed

theorem duration_rate_nonnegative (a : Parameters) (M : Tensor2) (v : CoordinatePoint) :
    0 ≤ durationRate a M v := div_nonneg (Real.sqrt_nonneg _) a.speed_pos.le

theorem source_duration_conformal (a : Parameters) (p v : CoordinatePoint) :
    durationRate a (sourceMetric a p) v = scalarSourceLapse a p * durationRate a metric v := by
  rw [source_metric_conformal]
  change Real.sqrt (-wickMatrixQuadratic (sourceFactor a p • metric) v)/a.speed = _
  rw [quadratic_scalar_multiple]
  rw [show -(sourceFactor a p*wickMatrixQuadratic metric v) =
    sourceFactor a p*(-wickMatrixQuadratic metric v) by ring,
    Real.sqrt_mul (source_factor_positive a p).le]
  change Real.sqrt (sourceFactor a p)*Real.sqrt (-wickMatrixQuadratic metric v)/a.speed =
    Real.sqrt (sourceFactor a p)*(Real.sqrt (-wickMatrixQuadratic metric v)/a.speed)
  ring

theorem duration_rate_vector_scaling (a : Parameters) (M : Tensor2) (v : CoordinatePoint)
    (epsilon : ℝ) (positive : 0 ≤ epsilon) : durationRate a M (epsilon • v) = epsilon * durationRate a M v := by
  have quadratic : wickMatrixQuadratic M (epsilon • v) = epsilon^2*wickMatrixQuadratic M v := by
    simp only [wickMatrixQuadratic,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold durationRate
  rw [quadratic,show -(epsilon^2*wickMatrixQuadratic M v)=epsilon^2*(-wickMatrixQuadratic M v) by ring,
    Real.sqrt_mul (sq_nonneg epsilon),Real.sqrt_sq positive]
  ring

theorem duration_integrand_error (a : Parameters) (p v : CoordinatePoint)
    (inside : p ∈ sourceDomain a) (small : |conformalFrequency a*p 0| ≤ (1:ℝ)/2) :
    |durationRate a (sourceMetric a p) v-durationRate a metric v| ≤
      2*(conformalFrequency a*p 0)^2*durationRate a metric v := by
  rw [source_duration_conformal,
    show scalarSourceLapse a p*durationRate a metric v-durationRate a metric v =
      (scalarSourceLapse a p-1)*durationRate a metric v by ring,abs_mul,
    abs_of_nonneg (duration_rate_nonnegative a metric v)]
  exact mul_le_mul_of_nonneg_right (protected_scale_error_bounds a p inside small).1
    (duration_rate_nonnegative a metric v)

theorem scaled_duration_integrand_error (a : Parameters) (epsilon B : ℝ) (p v : CoordinatePoint)
    (_he : 0 ≤ epsilon) (hB : 0 ≤ B) (pointBound : |p 0| ≤ B)
    (inside : epsilon • p ∈ sourceDomain a) (small : |conformalFrequency a*(epsilon • p) 0| ≤ (1:ℝ)/2) :
    |durationRate a (normalizedRescaledMetric a epsilon p) v-durationRate a metric v| ≤
      (2*conformalFrequency a^2*B^2)*epsilon^2*durationRate a metric v := by
  have bound := duration_integrand_error a (epsilon • p) v inside small
  change |durationRate a (sourceMetric a (epsilon • p)) v-durationRate a metric v| ≤ _
  apply bound.trans
  apply mul_le_mul_of_nonneg_right ?_ (duration_rate_nonnegative a metric v)
  have square : (p 0)^2 ≤ B^2 := by nlinarith [sq_abs (p 0),abs_nonneg (p 0)]
  simp only [Pi.smul_apply,smul_eq_mul]
  have estimate := mul_le_mul_of_nonneg_left square (show 0 ≤ 2*conformalFrequency a^2*epsilon^2 by positivity)
  nlinarith [estimate]

theorem duration_rate_continuous (a : Parameters) : Continuous (fun z : Tensor2 × CoordinatePoint => durationRate a z.1 z.2) := by
  unfold durationRate wickMatrixQuadratic
  fun_prop

theorem fixed_metric_scaled_path_comparison (a : Parameters) (y : ℝ → CoordinatePoint)
    (regular : ContDiff ℝ 1 y) (b e : ℝ) (order : b ≤ e) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ epsilon0 →
        (∀ s ∈ Icc b e, epsilon • y s ∈ sourceDomain a) ∧
        |(∫ s in b..e, durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s))-
          (∫ s in b..e, durationRate a metric (deriv y s))| ≤ C*epsilon^2 ∧
        (∫ s in b..e, durationRate a (sourceMetric a (epsilon • y s)) (deriv (fun t => epsilon • y t) s)) =
          epsilon*(∫ s in b..e, durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s)) := by
  have smoothDerivative : Continuous (deriv y) := regular.continuous_deriv (by norm_num)
  have compactPath : IsCompact (y '' Icc b e) := isCompact_Icc.image regular.continuous
  obtain ⟨epsilon0,B,he0,hB,pointBound,receiving⟩ := compact_dilation_receiving_domain a _ compactPath
  have flatContinuous : Continuous (fun s => durationRate a metric (deriv y s)) :=
    (duration_rate_continuous a).comp (continuous_const.prodMk smoothDerivative)
  obtain ⟨V0,velocityBound⟩ := (isCompact_Icc : IsCompact (Icc b e)).exists_bound_of_continuousOn
    (f := fun s => durationRate a metric (deriv y s)) flatContinuous.continuousOn
  let V := |V0|
  let A := 2*conformalFrequency a^2*B^2
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hV : 0 ≤ V := abs_nonneg V0
  refine ⟨epsilon0,A*V*(e-b),he0,mul_nonneg (mul_nonneg hA hV) (sub_nonneg.mpr order),?_⟩
  intro epsilon he heps
  have domain (s : ℝ) (hs : s ∈ Icc b e) := receiving epsilon he heps (y s) ⟨s,hs,rfl⟩
  have uniformBound (s : ℝ) (hs : s ∈ Icc b e) :
      |durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s)-
        durationRate a metric (deriv y s)| ≤ A*epsilon^2*V := by
    have timeBound : |y s 0| ≤ B :=
      (le_add_of_nonneg_right (norm_nonneg ((coordinateSpatialSplit (y s)).2))).trans (pointBound _ ⟨s,hs,rfl⟩)
    have estimate := scaled_duration_integrand_error a epsilon B (y s) (deriv y s) he hB.le timeBound
      (domain s hs).1 (domain s hs).2
    have vnorm : |durationRate a metric (deriv y s)| ≤ V0 := by
      simpa only [Real.norm_eq_abs] using velocityBound s hs
    have velocity : durationRate a metric (deriv y s) ≤ V :=
      (le_abs_self _).trans (vnorm.trans (le_abs_self V0))
    exact estimate.trans (mul_le_mul_of_nonneg_left velocity (mul_nonneg hA (sq_nonneg epsilon)))
  have curvedContinuous : Continuous (fun s => durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s)) := by
    change Continuous (fun s => durationRate a (sourceMetric a (epsilon • y s)) (deriv y s))
    exact (duration_rate_continuous a).comp
      (((source_metric_continuous a).comp (continuous_const.smul regular.continuous)).prodMk smoothDerivative)
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := b) (b := e) (C := A*epsilon^2*V) (f := fun s => durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s)-
      durationRate a metric (deriv y s))
    (fun s hs => by
      rw [uIoc_of_le order] at hs
      simpa only [Real.norm_eq_abs] using uniformBound s ⟨hs.1.le,hs.2⟩)
  refine ⟨fun s hs => (domain s hs).1,?_,?_⟩
  · rw [intervalIntegral.integral_sub (curvedContinuous.intervalIntegrable b e) (flatContinuous.intervalIntegrable b e)] at integralBound
    simp only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr order)] at integralBound
    convert integralBound using 1 <;> ring
  · rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    have derivative := ((regular.differentiable (by norm_num) s).hasDerivAt).const_smul epsilon
    change durationRate a (sourceMetric a (epsilon • y s)) (deriv (epsilon • y) s) = _
    rw [derivative.deriv,duration_rate_vector_scaling a _ _ epsilon he]
    rfl

end AASCKleinGordon.RecoveryComparison
