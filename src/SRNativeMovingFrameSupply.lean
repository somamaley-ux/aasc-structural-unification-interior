import SRNativeFrameOccupation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open scoped Matrix BigOperators

def srUnitAxialBoost (t r : ℝ) (hyperbolic : t^2-r^2=1) : SRMatrixFrame :=
  srScaledAxialBoostUnit t r 1 (by norm_num) hyperbolic

theorem sr_unit_axial_boost_isometry (t r : ℝ) (hyperbolic : t^2-r^2=1) :
    srFramePullback (srUnitAxialBoost t r hyperbolic : ComparisonMatrix) = comparisonUnitLorentz := by
  have h := sr_scaled_axial_boost_pullback t r 1 (Real.sqrt 1) hyperbolic (by norm_num)
  simpa only [one_smul] using h

theorem sr_unit_axial_boost_inverse (t r : ℝ) (hyperbolic : t^2-r^2=1) :
    (srUnitAxialBoost t r hyperbolic)⁻¹ = srUnitAxialBoost t (-r) (by nlinarith) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
      srScaledAxialBoostInverse]

theorem sr_unit_axial_boost_time (t r : ℝ) (hyperbolic : t^2-r^2=1) (z : SREvent) :
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) z).1 = t*z.1+r*z.2 0 := by
  have h := congrArg (fun v : CoordinatePoint => v 0)
    (sr_event_frame_coordinate_square (srUnitAxialBoost t r hyperbolic) z)
  simpa [srEventCoordinates,srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using h

theorem sr_spatial_first_coordinate_bounded_by_original_norm (x : SRSpace) : |x 0| ≤ ‖x‖ := by
  have h := EuclideanSpace.norm_sq_eq x
  norm_num [Fin.sum_univ_succ,Real.norm_eq_abs] at h
  nlinarith [sq_abs (x 0),abs_nonneg (x 0),norm_nonneg x,sq_nonneg (x 1),sq_nonneg (x 2)]

theorem sr_source_form_isometry_event_value (A : SRMatrixFrame)
    (isometry : srFramePullback (A : ComparisonMatrix) = comparisonUnitLorentz) (z : SREvent) :
    (srMatrixFrameEventLinear A z).1^2 - ‖(srMatrixFrameEventLinear A z).2‖^2 = z.1^2-‖z.2‖^2 := by
  change (srMatrixFrameEvent A z).1^2 - ‖(srMatrixFrameEvent A z).2‖^2 = _
  rw [← sr_coordinate_unit_quadratic_is_source_form,sr_event_frame_coordinate_square,
    ← sr_frame_pullback_quadratic,isometry,sr_coordinate_unit_quadratic_is_source_form]

theorem sr_unit_axial_boost_preserves_future (t r : ℝ) (hyperbolic : t^2-r^2=1)
    (positive : 0 < t) (z : SREvent) (future : z ∈ srRayFutureCone) :
    srMatrixFrameEvent (srUnitAxialBoost t r hyperbolic) z ∈ srRayFutureCone := by
  have bound := sr_spatial_first_coordinate_bounded_by_original_norm z.2
  have rbound : |r| < t := by nlinarith [sq_abs r,abs_nonneg r]
  have oldTime : 0 ≤ z.1 := (norm_nonneg z.2).trans future
  have oldBound : ‖z.2‖ ≤ z.1 := future
  have product : |r*z.2 0| ≤ |r| * ‖z.2‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left bound (abs_nonneg r)
  have slack := mul_nonneg (le_of_lt (sub_pos.mpr rbound)) oldTime
  have normSlack := mul_nonneg (abs_nonneg r) (sub_nonneg.mpr future)
  have time : 0 ≤ (srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) z).1 := by
    rw [sr_unit_axial_boost_time]
    nlinarith [neg_abs_le (r*z.2 0)]
  have q := sr_source_form_isometry_event_value (srUnitAxialBoost t r hyperbolic)
    (sr_unit_axial_boost_isometry t r hyperbolic) z
  have oldNorm : 0 ≤ z.1^2-‖z.2‖^2 := by
    have product := mul_nonneg (sub_nonneg.mpr oldBound) (add_nonneg oldTime (norm_nonneg z.2))
    nlinarith
  change ‖(srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) z).2‖ ≤
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) z).1
  nlinarith [norm_nonneg (srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) z).2]

theorem sr_unit_axial_boost_has_exact_original_cone_receipt (t r : ℝ)
    (hyperbolic : t^2-r^2=1) (positive : 0 < t) :
    srMatrixFrameEvent (srUnitAxialBoost t r hyperbolic) '' srRayFutureCone = srRayFutureCone := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact sr_unit_axial_boost_preserves_future t r hyperbolic positive x hx
  · intro hz
    refine ⟨srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic)⁻¹ z,?_,?_⟩
    · rw [sr_unit_axial_boost_inverse]
      exact sr_unit_axial_boost_preserves_future t (-r) (by nlinarith) positive z hz
    · change srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic)
        (srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic)⁻¹ z) = z
      rw [← sr_event_frame_mul,mul_inv_cancel,sr_event_frame_one]

theorem sr_all_future_unit_axial_boosts_are_actually_supplied (t r : ℝ)
    (hyperbolic : t^2-r^2=1) (positive : 0 < t) :
    srUnitAxialBoost t r hyperbolic ∈ srNativeFrameComparisons := by
  refine ⟨sr_unit_axial_boost_isometry t r hyperbolic,?_,
    sr_unit_axial_boost_has_exact_original_cone_receipt t r hyperbolic positive⟩
  change 0 < (srScaledAxialBoost t r (Real.sqrt 1)).det
  rw [sr_scaled_axial_boost_determinant,hyperbolic]
  norm_num

def srConcreteMovingBoost : SRMatrixFrame := srUnitAxialBoost (5/4) (3/4) (by norm_num)

theorem sr_native_comparison_family_contains_genuine_moving_frame :
    srConcreteMovingBoost ∈ srNativeFrameComparisons ∧
      ((srConcreteMovingBoost : ComparisonMatrix).mulVec (originalComparisonProbe 0)) 1 = 3/4 := by
  refine ⟨sr_all_future_unit_axial_boosts_are_actually_supplied (5/4) (3/4) (by norm_num) (by norm_num),?_⟩
  norm_num [srConcreteMovingBoost,srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
    originalComparisonProbe,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

#print axioms sr_all_future_unit_axial_boosts_are_actually_supplied
#print axioms sr_native_comparison_family_contains_genuine_moving_frame
end AASCKleinGordon.CanonicalLicensing.SRIntegration
