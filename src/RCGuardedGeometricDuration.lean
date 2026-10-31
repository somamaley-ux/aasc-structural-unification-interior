import RCDurationComparison

/-! Future-timelike applicability of the actual geometric-duration query.
This certifies geometry on a supplied path, not occupation of an independent
physical clock apparatus or equality to its reading without calibration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology Interval
namespace AASCKleinGordon.RecoveryComparison
attribute [local instance] Classical.propDecidable

def futureTimelikeMargin (y : ℝ → CoordinatePoint) (b e delta : ℝ) : Prop :=
  0 < delta ∧ ∀ s ∈ Icc b e, 0 < deriv y s 0 ∧
    wickMatrixQuadratic metric (deriv y s) ≤ -delta*‖deriv y s‖^2

def geometricDurationApplicable (a : Parameters) (y : ℝ → CoordinatePoint) (b e : ℝ) : Prop :=
  b ≤ e ∧ DifferentiableOn ℝ y (Icc b e) ∧
    ∀ s ∈ Icc b e, y s ∈ sourceDomain a ∧ 0 < deriv y s 0 ∧
      wickMatrixQuadratic (sourceMetric a (y s)) (deriv y s) < 0

def geometricDurationRead (a : Parameters) (y : ℝ → CoordinatePoint) (b e : ℝ) : Option ℝ :=
  if geometricDurationApplicable a y b e then
    some (∫ s in b..e, durationRate a (sourceMetric a (y s)) (deriv y s)) else none

theorem scaled_future_timelike (a : Parameters) (y : ℝ → CoordinatePoint)
    (regular : ContDiff ℝ 1 y) (b e delta epsilon : ℝ) (margin : futureTimelikeMargin y b e delta)
    (he : 0 < epsilon) (_domain : ∀ s ∈ Icc b e, epsilon • y s ∈ sourceDomain a)
    (s : ℝ) (hs : s ∈ Icc b e) :
    0 < deriv (fun t => epsilon • y t) s 0 ∧
      wickMatrixQuadratic (sourceMetric a (epsilon • y s)) (deriv (fun t => epsilon • y t) s) < 0 := by
  have derivative := ((regular.differentiable (by norm_num) s).hasDerivAt).const_smul epsilon
  change 0 < deriv (epsilon • y) s 0 ∧
    wickMatrixQuadratic (sourceMetric a (epsilon • y s)) (deriv (epsilon • y) s) < 0
  rw [derivative.deriv]
  have point := margin.2 s hs
  have nonzero : deriv y s ≠ 0 := by intro zero;rw [zero] at point;simpa using point.1
  have negative : wickMatrixQuadratic metric (deriv y s) < 0 := by
    have product := mul_pos margin.1 (sq_pos_of_pos (norm_pos_iff.mpr nonzero))
    linarith [point.2]
  refine ⟨by simpa only [Pi.smul_apply,smul_eq_mul] using mul_pos he point.1,?_⟩
  rw [source_metric_conformal]
  change wickMatrixQuadratic (sourceFactor a (epsilon • y s) • metric) (epsilon • deriv y s) < 0
  rw [quadratic_scalar_multiple]
  have scale : wickMatrixQuadratic metric (epsilon • deriv y s) = epsilon^2*wickMatrixQuadratic metric (deriv y s) := by
    simp only [wickMatrixQuadratic,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [scale]
  exact mul_neg_of_pos_of_neg (source_factor_positive a _) (mul_neg_of_pos_of_neg (sq_pos_of_pos he) negative)

theorem guarded_scaled_geometric_duration (a : Parameters) (y : ℝ → CoordinatePoint)
    (regular : ContDiff ℝ 1 y) (b e delta : ℝ) (order : b ≤ e)
    (margin : futureTimelikeMargin y b e delta) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ 0 ≤ C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
      geometricDurationApplicable a (fun t => epsilon • y t) b e ∧
      ∃ value : ℝ, geometricDurationRead a (fun t => epsilon • y t) b e = some value ∧
        |value-epsilon*(∫ s in b..e, durationRate a metric (deriv y s))| ≤ C*epsilon^3 := by
  obtain ⟨epsilon0,C,positive,hC,comparison⟩ := fixed_metric_scaled_path_comparison a y regular b e order
  refine ⟨epsilon0,C,positive,hC,?_⟩
  intro epsilon he heps
  obtain ⟨domain,error,scaling⟩ := comparison epsilon he.le heps
  have applicable : geometricDurationApplicable a (fun t => epsilon • y t) b e := by
    refine ⟨order,?_,?_⟩
    · exact (regular.differentiable (by norm_num)).const_smul epsilon |>.differentiableOn
    · intro s hs
      exact ⟨domain s hs,(scaled_future_timelike a y regular b e delta epsilon margin he domain s hs).1,
        (scaled_future_timelike a y regular b e delta epsilon margin he domain s hs).2⟩
  refine ⟨applicable,
    (∫ s in b..e, durationRate a (sourceMetric a (epsilon • y s)) (deriv (fun t => epsilon • y t) s)),
    by simp only [geometricDurationRead,if_pos applicable],?_⟩
  rw [scaling,←mul_sub,abs_mul,abs_of_pos he]
  have scaled := mul_le_mul_of_nonneg_left error he.le
  convert scaled using 1 <;> ring

end AASCKleinGordon.RecoveryComparison
