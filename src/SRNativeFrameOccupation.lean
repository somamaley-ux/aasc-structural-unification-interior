import SRCalibratedFrameTheorem

/-! A native occupation witness AFTER the universal frame reconstruction.
This witness family is defined by the chosen model's exact isometries, as in
SR 15.7. Its membership is not the proof of general frame classification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

theorem sr_event_frame_one (z : SREvent) : srMatrixFrameEventLinear 1 z = z := by
  apply srEventCoordinates.injective
  change srEventCoordinates (srMatrixFrameEvent 1 z) = _
  rw [sr_event_frame_coordinate_square]
  simp

theorem sr_event_frame_mul (A B : SRMatrixFrame) (z : SREvent) :
    srMatrixFrameEventLinear (A*B) z = srMatrixFrameEventLinear A (srMatrixFrameEventLinear B z) := by
  apply srEventCoordinates.injective
  change srEventCoordinates (srMatrixFrameEvent (A*B) z) =
    srEventCoordinates (srMatrixFrameEvent A (srMatrixFrameEvent B z))
  rw [sr_event_frame_coordinate_square,sr_event_frame_coordinate_square,sr_event_frame_coordinate_square]
  change ((A : ComparisonMatrix)*(B : ComparisonMatrix)).mulVec _ = _
  exact (Matrix.mulVec_mulVec _ _ _).symm

theorem sr_event_frame_inverse_left (A : SRMatrixFrame) (z : SREvent) :
    srMatrixFrameEventLinear A⁻¹ (srMatrixFrameEventLinear A z) = z := by
  rw [← sr_event_frame_mul,inv_mul_cancel,sr_event_frame_one]

theorem sr_frame_cone_receipt_mul (A B : SRMatrixFrame)
    (ha : srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone)
    (hb : srMatrixFrameEvent B '' srRayFutureCone = srRayFutureCone) :
    srMatrixFrameEvent (A*B) '' srRayFutureCone = srRayFutureCone := by
  calc
    srMatrixFrameEvent (A*B) '' srRayFutureCone =
        srMatrixFrameEvent A '' (srMatrixFrameEvent B '' srRayFutureCone) := by
      rw [Set.image_image]
      congr 1
      exact funext (sr_event_frame_mul A B)
    _ = srRayFutureCone := by rw [hb,ha]

theorem sr_frame_cone_receipt_inverse (A : SRMatrixFrame)
    (ha : srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone) :
    srMatrixFrameEvent A⁻¹ '' srRayFutureCone = srRayFutureCone := by
  have cancel : srMatrixFrameEvent A⁻¹ '' (srMatrixFrameEvent A '' srRayFutureCone) =
      srRayFutureCone := by
    rw [Set.image_image]
    have same : (fun z => srMatrixFrameEvent A⁻¹ (srMatrixFrameEvent A z)) = id :=
      funext (sr_event_frame_inverse_left A)
    rw [same,Set.image_id]
  rwa [ha] at cancel

def srNativeFrameComparisons : Subgroup SRMatrixFrame where
  carrier := {A | srFramePullback (A : ComparisonMatrix) = comparisonUnitLorentz ∧
    0 < (A : ComparisonMatrix).det ∧ srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone}
  one_mem' := by
    refine ⟨?_,?_,?_⟩
    · simp [srFramePullback]
    · norm_num
    · have action : (srMatrixFrameEvent 1 : SREvent → SREvent) = id := funext sr_event_frame_one
      rw [action,Set.image_id]
  mul_mem' := by
    intro A B ha hb
    refine ⟨?_,?_,sr_frame_cone_receipt_mul A B ha.2.2 hb.2.2⟩
    · change srFramePullback ((A : ComparisonMatrix)*(B : ComparisonMatrix)) = _
      rw [sr_frame_pullback_composition,ha.1]
      exact hb.1
    · change 0 < (((A : ComparisonMatrix)*(B : ComparisonMatrix)).det)
      rw [Matrix.det_mul]
      exact mul_pos ha.2.1 hb.2.1
  inv_mem' := by
    intro A ha
    have cancel : (A : ComparisonMatrix)*(A⁻¹ : SRMatrixFrame) = (1 : ComparisonMatrix) := by
      rw [← Units.val_mul,mul_inv_cancel]
      rfl
    refine ⟨?_,?_,sr_frame_cone_receipt_inverse A ha.2.2⟩
    · have h := congrArg srFramePullback cancel
      rw [sr_frame_pullback_composition,ha.1] at h
      simpa [srFramePullback] using h
    · have product := congrArg Matrix.det cancel
      rw [Matrix.det_mul,Matrix.det_one] at product
      by_contra hn
      have nonpos := mul_nonpos_of_nonneg_of_nonpos ha.2.1.le (le_of_not_gt hn)
      linarith

theorem sr_original_rest_frame_event_value (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (z : SREvent) :
    srMatrixFrameEventLinear (srRestCoordinateUnit Q) z = (z.1,Q z.2) := by
  apply srEventCoordinates.injective
  change srEventCoordinates (srMatrixFrameEvent (srRestCoordinateUnit Q) z) = _
  rw [sr_event_frame_coordinate_square,sr_rest_coordinate_unit_apply,
    srEventCoordinates.symm_apply_apply]

theorem sr_native_rest_frames_preserve_original_cone (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) :
    srMatrixFrameEvent (srRestCoordinateUnit Q) '' srRayFutureCone = srRayFutureCone := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change ‖(srMatrixFrameEventLinear (srRestCoordinateUnit Q) x).2‖ ≤
      (srMatrixFrameEventLinear (srRestCoordinateUnit Q) x).1
    rw [sr_original_rest_frame_event_value]
    simpa using hx
  · intro hz
    refine ⟨(z.1,Q.symm z.2),?_,?_⟩
    · change ‖Q.symm z.2‖ ≤ z.1
      simpa using hz
    · change srMatrixFrameEventLinear (srRestCoordinateUnit Q) (z.1,Q.symm z.2) = z
      rw [sr_original_rest_frame_event_value]
      simp

def srNativeOccupiedFrameSource (μ0 : ℝ) (mass : 0 < μ0) : SRCalibratedFrameSource μ0 where
  comparisons := srNativeFrameComparisons
  tickSpan := 1
  tickPositive := by norm_num
  coneReceipt := fun _ h => h.2.2
  orientation := fun _ h => h.2.1
  originalRestFamily := by
    intro Q proper
    have role := sr_original_spatial_frame_has_exact_rest_role Q proper
    exact ⟨role.1,role.2.2,sr_native_rest_frames_preserve_original_cone Q⟩
  sameOriginalRestTick := by
    intro d positive admitted
    have form := admitted.1
    have value := congrArg (fun M : ComparisonMatrix => M 0 0) form
    norm_num [srDilationUnit,srFramePullback,comparisonUnitLorentz,Matrix.transpose_apply,
      Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_succ] at value
    have unit : d=1 := by nlinarith
    rw [unit,sr_original_rest_tick_actual_readout μ0 1 mass]
    norm_num

#print axioms srNativeOccupiedFrameSource
end AASCKleinGordon.CanonicalLicensing.SRIntegration
