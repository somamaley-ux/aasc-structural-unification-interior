import SRCalibratedFrameTheorem

/-! Residual scale of the native completed future cone and its positive rest-clock readings. -/

noncomputable section
set_option autoImplicit false
namespace AASCOccupiedConeScale
open AASCMetricConstruction AASCMetricConstruction.SRIntegration
open AASCKleinGordon.CanonicalLicensing.SRIntegration
open scoped Matrix

private theorem dilation_event (d : ℝ) (hd : 0 < d) (z : SREvent) :
    srMatrixFrameEvent (srDilationUnit d hd.ne') z = d • z := by
  apply srEventCoordinates.injective
  rw [sr_event_frame_coordinate_square, map_smul]
  change (d • (1 : ComparisonMatrix)).mulVec _ = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem inCone (t : ℝ) (ht : 0 < t) (z : SREvent) :
    t • z ∈ srRayFutureCone ↔ z ∈ srRayFutureCone := by
  change ‖t • z.2‖ ≤ t * z.1 ↔ ‖z.2‖ ≤ z.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_le_mul_iff_right₀ ht

/-- A dilation preserves and reflects the completed-order answer on every
pair of events, including events that the order leaves incomparable. -/
theorem dilation_preserves_every_order_answer (d : ℝ) (hd : 0 < d) (x y : SREvent) :
    srMatrixFrameEvent (srDilationUnit d hd.ne') y -
      srMatrixFrameEvent (srDilationUnit d hd.ne') x ∈ srRayFutureCone ↔ y - x ∈ srRayFutureCone := by
  rw [dilation_event d hd, dilation_event d hd, ← smul_sub]
  exact inCone d hd (y - x)

/-- Dilations act bijectively on the original completed future cone. -/
theorem dilation_preserves_completed_cone (d : ℝ) (hd : 0 < d) :
    srMatrixFrameEvent (srDilationUnit d hd.ne') '' srRayFutureCone = srRayFutureCone := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [dilation_event d hd]
    exact (inCone d hd w).2 hw
  · intro hz
    refine ⟨d⁻¹ • z, (inCone d⁻¹ (inv_pos.mpr hd) z).2 hz, ?_⟩
    rw [dilation_event d hd, smul_smul, mul_inv_cancel₀ hd.ne', one_smul]

private theorem coefficient_unique {a b : ℝ}
    (same : a • comparisonUnitLorentz = b • comparisonUnitLorentz) : a = b := by
  have entry := congrArg (fun m : ComparisonMatrix => m 0 0) same
  simpa [comparisonUnitLorentz, Matrix.diagonal] using entry

/-- On invertible linear comparisons, every positive conformal factor and
only those factors occur before a clock reading is imposed. -/
theorem completed_cone_factor_range (k : ℝ) :
    (∃ A : SRMatrixFrame,
      srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone ∧
      srFramePullback (A : ComparisonMatrix) = k • comparisonUnitLorentz) ↔ 0 < k := by
  constructor
  · rintro ⟨A, cone, factor⟩
    obtain ⟨c, hc, pullback⟩ := sr_exact_completed_source_cone_constructs_positive_conformal_frame A cone
    exact (coefficient_unique (pullback.symm.trans factor)) ▸ hc
  · intro hk
    let d := Real.sqrt k
    have hd : 0 < d := Real.sqrt_pos.mpr hk
    have hs : d * d = k := by simpa [d, sq] using Real.sq_sqrt hk.le
    refine ⟨srDilationUnit d hd.ne', dilation_preserves_completed_cone d hd, ?_⟩
    change (d • (1 : ComparisonMatrix)).transpose * comparisonUnitLorentz * (d • 1) = _
    simp [Matrix.transpose_smul, smul_smul, hs]

/-- Each positive span is actually recorded by the native coasting rest
clock. A positive dilation preserves that reading precisely at unit scale. -/
theorem occupied_rest_reading_fixes_dilation (mass span d : ℝ)
    (hmass : 0 < mass) (hspan : 0 < span) (hd : 0 < d) :
    srNativeClockUseValid mass (srOriginalRestTickUse mass span) ∧
    srNativeClockUseValid mass (srOriginalRestTickUse mass (d * span)) ∧
    srMatrixFrameEvent (srDilationUnit d hd.ne') '' srRayFutureCone = srRayFutureCone ∧
    (srNativeClockActualInterval mass (srOriginalRestTickUse mass (d * span)) =
      srNativeClockActualInterval mass (srOriginalRestTickUse mass span) ↔ d = 1) := by
  refine ⟨sr_original_rest_tick_use_valid mass span hmass hspan,
    sr_original_rest_tick_use_valid mass (d * span) hmass (mul_pos hd hspan),
    dilation_preserves_completed_cone d hd, ?_⟩
  simp only [sr_original_rest_tick_actual_readout _ _ hmass]
  constructor
  · intro eq
    have zero : (d - 1) * span = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_right hspan.ne')
  · rintro rfl
    exact one_mul span

#print axioms dilation_preserves_every_order_answer
#print axioms dilation_preserves_completed_cone
#print axioms completed_cone_factor_range
#print axioms occupied_rest_reading_fixes_dilation

end AASCOccupiedConeScale
