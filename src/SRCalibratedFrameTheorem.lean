import SRRestStabilizerSpatialEquivalence

/-! SR 6.5--6.6 on the occupied native receiving branch. The source conditions
are exact cone receipt, orientation, a complete rest-rotation family and one
actual common rest-clock pair with rest-only calibration. Metric preservation
of arbitrary admitted comparisons is proved, not a field of this source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open scoped Matrix BigOperators

def srOriginalRestTickUse (_μ0 T : ℝ) : SRNativeClockUse SRSpace :=
  ⟨(0,0,srNativeRestClock 0),0,T,T⟩

theorem sr_original_rest_tick_actual_readout (μ0 T : ℝ) (mass : 0 < μ0) :
    srNativeClockActualInterval μ0 (srOriginalRestTickUse μ0 T) = T := by
  change (srNativeClockCoastFlow μ0 (T-0) (srNativeRestClock (0:SRSpace))).reading -
    (srNativeClockCoastFlow μ0 (0-0) (srNativeRestClock (0:SRSpace))).reading = T
  rw [(sr_native_rest_clock_actual_coasting_record μ0 mass (0:SRSpace) (T-0)).2.1,
    (sr_native_rest_clock_actual_coasting_record μ0 mass (0:SRSpace) (0-0)).2.1]
  ring

theorem sr_original_rest_tick_use_valid (μ0 T : ℝ) (mass : 0 < μ0) (tick : 0 < T) :
    srNativeClockUseValid μ0 (srOriginalRestTickUse μ0 T) := by
  refine ⟨?_,tick.le,?_⟩
  · simpa [srOriginalRestTickUse,srNativeRestClock,srNativeClockMass] using mass
  · exact (sr_original_rest_tick_actual_readout μ0 T mass).symm

structure SRCalibratedFrameSource (μ0 : ℝ) where
  comparisons : Subgroup SRMatrixFrame
  tickSpan : ℝ
  tickPositive : 0 < tickSpan
  coneReceipt : ∀ A ∈ comparisons,
    srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone
  orientation : ∀ A ∈ comparisons, 0 < (A : ComparisonMatrix).det
  originalRestFamily : ∀ Q : SRSpace ≃ₗᵢ[ℝ] SRSpace,
    LinearMap.det Q.toLinearMap = 1 → srRestCoordinateUnit Q ∈ comparisons
  sameOriginalRestTick : ∀ d : ℝ, ∀ hd : 0 < d,
    srDilationUnit d hd.ne' ∈ comparisons →
      d*tickSpan = srNativeClockActualInterval μ0 (srOriginalRestTickUse μ0 tickSpan)

theorem sr_original_source_calibrated_frames_preserve_constructed_metric
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons) :
    srFramePullback (A : ComparisonMatrix) = comparisonUnitLorentz := by
  have allRest : ∀ R : SRMatrixFrame, srIsOriginalProperRestRotation R → R ∈ source.comparisons := by
    intro R role
    obtain ⟨Q,proper,same⟩ := (sr_original_rest_role_iff_spatial_so3 R).mp role
    rw [← same]
    exact source.originalRestFamily Q proper
  obtain ⟨κ,positive,conformal⟩ := sr_exact_completed_source_cone_constructs_positive_conformal_frame
    A (source.coneReceipt A admitted)
  obtain ⟨S,hs,sform,soriented,t,r,column⟩ :=
    sr_actual_original_spatial_rotations_align_every_frame_column
      source.comparisons allRest A
  have saform : srFramePullback ((S*A : SRMatrixFrame) : ComparisonMatrix) = κ • comparisonUnitLorentz := by
    change srFramePullback ((S : ComparisonMatrix)*(A : ComparisonMatrix)) = _
    rw [sr_frame_pullback_composition,sform]
    exact conformal
  have clock : comparisonQuadratic comparisonUnitLorentz
      (((S*A : SRMatrixFrame) : ComparisonMatrix).mulVec (originalComparisonProbe 0)) = κ := by
    rw [← sr_frame_pullback_quadratic,saform]
    norm_num [comparisonQuadratic,comparisonUnitLorentz,originalComparisonProbe,
      Matrix.diagonal,Fin.sum_univ_succ]
  rw [column] at clock
  have hyperbolic : t^2-r^2=κ := by
    norm_num [comparisonQuadratic,comparisonUnitLorentz,Matrix.diagonal,
      Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at clock
    nlinarith
  have boost := sr_aligned_original_frame_constructs_scaled_boost source.comparisons A S κ t r
    positive hyperbolic admitted hs (source.orientation A admitted) soriented conformal sform column
    allRest
  have sameTick : ∀ d : ℝ, ∀ hd : 0 < d,
      srDilationUnit d hd.ne' ∈ source.comparisons → d*source.tickSpan=source.tickSpan := by
    intro d hd member
    exact (source.sameOriginalRestTick d hd member).trans
      (sr_original_rest_tick_actual_readout μ0 source.tickSpan mass)
  have unitScale := sr_same_original_rest_tick_eliminates_scaled_boost
    source.comparisons t r κ source.tickSpan positive source.tickPositive hyperbolic boost
    (allRest _ sr_spatial_half_turn_is_original_proper_rest_rotation) sameTick
  simpa only [unitScale,one_smul] using conformal

theorem sr_admitted_frames_preserve_same_source_derived_form
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (A : SRMatrixFrame) (admitted : A ∈ source.comparisons) (z : SREvent) :
    srOriginalOrderQuadratic (srMatrixFrameEvent A z) = srOriginalOrderQuadratic z := by
  rw [sr_original_order_quadratic_computed,sr_original_order_quadratic_computed,
    ← sr_coordinate_unit_quadratic_is_source_form,← sr_coordinate_unit_quadratic_is_source_form,
    sr_event_frame_coordinate_square,← sr_frame_pullback_quadratic,
    sr_original_source_calibrated_frames_preserve_constructed_metric μ0 mass source A admitted]

#print axioms sr_original_source_calibrated_frames_preserve_constructed_metric
#print axioms sr_admitted_frames_preserve_same_source_derived_form
end AASCKleinGordon.CanonicalLicensing.SRIntegration
