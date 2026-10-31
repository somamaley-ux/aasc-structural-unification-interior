import SRPassiveClockUseTransport

/-! Original translation-normalizing homeomorphisms are realized by the
constructed affine map before applying the calibrated frame/clock theorems.
No affine or Lorentz map is the input type of the original event comparison. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

def srOriginalFrameUnit (F : SREvent ≃ₜ SREvent)
    (normalizes : ∀ v : SREvent, ∃ w : SREvent, ∀ x : SREvent, F (x+v)=F x+w) : SRMatrixFrame :=
  Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((srEventCoordinates.symm.trans (srConstructedInvertibleFrameDisplacement F normalizes).toLinearEquiv).trans
      srEventCoordinates))

theorem sr_original_frame_unit_realizes_constructed_displacement (F : SREvent ≃ₜ SREvent)
    (normalizes : ∀ v : SREvent, ∃ w : SREvent, ∀ x : SREvent, F (x+v)=F x+w)
    (z : SREvent) : srMatrixFrameEventLinear (srOriginalFrameUnit F normalizes) z =
      srConstructedInvertibleFrameDisplacement F normalizes z := by
  apply srEventCoordinates.injective
  change srEventCoordinates (srMatrixFrameEvent (srOriginalFrameUnit F normalizes) z) = _
  rw [sr_event_frame_coordinate_square]
  change (LinearMap.toMatrix'
    ((srEventCoordinates.symm.trans (srConstructedInvertibleFrameDisplacement F normalizes).toLinearEquiv).trans
      srEventCoordinates).toLinearMap).mulVec (srEventCoordinates z) = _
  rw [LinearMap.toMatrix'_mulVec]
  change srEventCoordinates (srConstructedInvertibleFrameDisplacement F normalizes
    (srEventCoordinates.symm (srEventCoordinates z))) = _
  rw [srEventCoordinates.symm_apply_apply]

theorem sr_original_event_frame_is_constructed_affine (F : SREvent ≃ₜ SREvent)
    (normalizes : ∀ v : SREvent, ∃ w : SREvent, ∀ x : SREvent, F (x+v)=F x+w)
    (z : SREvent) : F z = srMatrixFrameEventLinear (srOriginalFrameUnit F normalizes) z + F 0 := by
  rw [sr_original_frame_unit_realizes_constructed_displacement]
  change F z = (F z-F 0)+F 0
  abel

structure SROriginalAdmittedFrame (μ0 : ℝ) (source : SRCalibratedFrameSource μ0) where
  eventMap : SREvent ≃ₜ SREvent
  normalizesOriginalTranslations : ∀ v : SREvent, ∃ w : SREvent,
    ∀ x : SREvent, eventMap (x+v)=eventMap x+w
  admitted : srOriginalFrameUnit eventMap normalizesOriginalTranslations ∈ source.comparisons

def srOriginalFrameClockUse {μ0 : ℝ} {source : SRCalibratedFrameSource μ0}
    (F : SROriginalAdmittedFrame μ0 source) (c : SRNativeClockUse SRSpace) : SRNativeClockUse SRSpace :=
  srPassiveClockUse μ0 (srOriginalFrameUnit F.eventMap F.normalizesOriginalTranslations) (F.eventMap 0) c

theorem sr_original_admitted_frame_metric_displacement_square
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (F : SROriginalAdmittedFrame μ0 source) (x y : SREvent) :
    srOriginalOrderQuadratic (F.eventMap y-F.eventMap x) = srOriginalOrderQuadratic (y-x) := by
  rw [sr_original_event_frame_is_constructed_affine F.eventMap F.normalizesOriginalTranslations y,
    sr_original_event_frame_is_constructed_affine F.eventMap F.normalizesOriginalTranslations x,
    add_sub_add_right_eq_sub,← map_sub]
  exact sr_admitted_frames_preserve_same_source_derived_form μ0 mass source _ F.admitted (y-x)

theorem sr_original_frame_clock_marked_time_is_same_event
    (μ0 : ℝ) (source : SRCalibratedFrameSource μ0) (F : SROriginalAdmittedFrame μ0 source)
    (r : SRClockRecord) (σ : ℝ) :
    srPassiveMarkedTime μ0 (srOriginalFrameUnit F.eventMap F.normalizesOriginalTranslations)
      (F.eventMap 0) r σ = (F.eventMap (srMarkedClockEvent μ0 r σ)).1 := by
  unfold srPassiveMarkedTime
  rw [← sr_original_event_frame_is_constructed_affine]

theorem sr_original_admitted_frame_transports_actual_clock_event
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (F : SROriginalAdmittedFrame μ0 source) (c : SRNativeClockUse SRSpace) (σ : ℝ)
    (positive : 0 < srNativeClockMass μ0 c.record.2.2) :
    srMarkedClockEvent μ0 (srOriginalFrameClockUse F c).record
      ((F.eventMap (srMarkedClockEvent μ0 c.record σ)).1) = F.eventMap (srMarkedClockEvent μ0 c.record σ) := by
  rw [← sr_original_frame_clock_marked_time_is_same_event μ0 source F c.record σ]
  exact (sr_passive_same_marked_clock_event_square μ0 mass source _ F.admitted
    (F.eventMap 0) c.record σ positive).trans
      (sr_original_event_frame_is_constructed_affine F.eventMap F.normalizesOriginalTranslations _).symm

theorem sr_original_admitted_frame_preserves_clock_use_and_failure
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (F : SROriginalAdmittedFrame μ0 source) (c : SRNativeClockUse SRSpace) :
    (srNativeClockUseValid μ0 (srOriginalFrameClockUse F c) ↔ srNativeClockUseValid μ0 c) ∧
      srClockCertification μ0 (srOriginalFrameClockUse F c) = srClockCertification μ0 c :=
  ⟨sr_passive_clock_use_has_exact_original_eligibility μ0 mass source _ F.admitted (F.eventMap 0) c,
    sr_passive_clock_certification_and_failure_same μ0 mass source _ F.admitted (F.eventMap 0) c⟩

#print axioms sr_original_event_frame_is_constructed_affine
#print axioms sr_original_admitted_frame_metric_displacement_square
#print axioms sr_original_admitted_frame_transports_actual_clock_event
end AASCKleinGordon.CanonicalLicensing.SRIntegration
