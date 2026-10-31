import SROriginalAffineFrameClockAttachment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

theorem sr_admitted_frame_transports_actual_positive_rays
    (μ0 : ℝ) (source : SRCalibratedFrameSource μ0) (A : SRMatrixFrame)
    (admitted : A ∈ source.comparisons) (z : SREvent) (ray : z ∈ srOriginalFutureRayIncrements) :
    srMatrixFrameEventLinear A z ∈ srOriginalFutureRayIncrements := by
  have boundary := sr_exact_original_cone_frame_preserves_boundary
    (srMatrixFrameEvent A) (source.coneReceipt A admitted) z ray.2
  have oldNonzero : z ≠ 0 := by
    intro same
    have time := congrArg Prod.fst same
    have positive : 0 < z.1 := ray.1
    simp only [Prod.fst_zero] at time
    linarith
  have newNonzero : srMatrixFrameEventLinear A z ≠ 0 := by
    intro zero
    exact oldNonzero ((srMatrixFrameEventLinear A).injective (zero.trans (map_zero _).symm))
  have nonnegative : 0 ≤ (srMatrixFrameEventLinear A z).1 :=
    (norm_nonneg _).trans_eq boundary
  have positive : 0 < (srMatrixFrameEventLinear A z).1 := by
    by_contra hn
    have time : (srMatrixFrameEventLinear A z).1 = 0 := le_antisymm (le_of_not_gt hn) nonnegative
    have spatial : (srMatrixFrameEventLinear A z).2 = 0 := norm_eq_zero.mp (boundary.trans time)
    exact newNonzero (Prod.ext time spatial)
  exact ⟨positive,boundary⟩

theorem sr_original_affine_frame_transports_actual_ray_leg
    (μ0 : ℝ) (source : SRCalibratedFrameSource μ0) (F : SROriginalAdmittedFrame μ0 source)
    (p q : SREvent) (ray : q-p ∈ srOriginalFutureRayIncrements) :
    F.eventMap q-F.eventMap p ∈ srOriginalFutureRayIncrements := by
  rw [sr_original_event_frame_is_constructed_affine F.eventMap F.normalizesOriginalTranslations q,
    sr_original_event_frame_is_constructed_affine F.eventMap F.normalizesOriginalTranslations p,
    add_sub_add_right_eq_sub,← map_sub]
  exact sr_admitted_frame_transports_actual_positive_rays μ0 source _ F.admitted (q-p) ray

theorem sr_every_finite_original_pulse_protocol_has_frame_natural_legs
    (μ0 : ℝ) (source : SRCalibratedFrameSource μ0) (F : SROriginalAdmittedFrame μ0 source)
    (ℓ : ℝ) (length : 0 < ℓ) (n : SRSpace) (unit : ‖n‖=1) (N : ℕ) :
    ∀ k : Fin N,
      F.eventMap (srNativeProtocolReflection ℓ n k.val)-
        F.eventMap (srNativeProtocolDeparture ℓ k.val) ∈ srOriginalFutureRayIncrements ∧
      F.eventMap (srNativeProtocolReturn ℓ k.val)-
        F.eventMap (srNativeProtocolReflection ℓ n k.val) ∈ srOriginalFutureRayIncrements := by
  intro k
  exact ⟨sr_original_affine_frame_transports_actual_ray_leg μ0 source F _ _
    (sr_native_protocol_forward_leg_is_original_ray ℓ length n unit k.val),
    sr_original_affine_frame_transports_actual_ray_leg μ0 source F _ _
    (sr_native_protocol_return_leg_is_original_ray ℓ length n unit k.val)⟩

theorem sr_every_finite_original_return_tick_has_same_source_frame_reading
    (μ0 : ℝ) (mass : 0 < μ0) (source : SRCalibratedFrameSource μ0)
    (F : SROriginalAdmittedFrame μ0 source) (ℓ : ℝ) (N : ℕ) :
    ∀ k : Fin N,
      (srNativeCoastingMarkedRecord μ0
        (srPassiveClockRecord μ0 (srOriginalFrameUnit F.eventMap F.normalizesOriginalTranslations)
          (F.eventMap 0) (0,0,srNativeRestClock 0))
        ((F.eventMap (srMarkedClockEvent μ0 (0,0,srNativeRestClock 0)
          (srNativeProtocolReturn (E:=SRSpace) ℓ k.val).1)).1)).2.reading = 2*((k.val:ℝ)+1)*ℓ := by
  intro k
  have positive : 0 < srNativeClockMass μ0 (srNativeRestClock (0:SRSpace)) := by
    simpa [srNativeClockMass,srNativeRestClock] using mass
  rw [← sr_original_frame_clock_marked_time_is_same_event μ0 source F,
    sr_passive_same_marked_clock_reading_square μ0 mass source _ F.admitted _ _ _ positive]
  change (srNativeClockCoastFlow μ0 ((srNativeProtocolReturn (E:=SRSpace) ℓ k.val).1-0)
    (srNativeRestClock (0:SRSpace))).reading = _
  rw [(sr_native_rest_clock_actual_coasting_record μ0 mass (0:SRSpace) _).2.1]
  simp [srNativeProtocolReturn]

#print axioms sr_every_finite_original_pulse_protocol_has_frame_natural_legs
#print axioms sr_every_finite_original_return_tick_has_same_source_frame_reading
end AASCKleinGordon.CanonicalLicensing.SRIntegration
