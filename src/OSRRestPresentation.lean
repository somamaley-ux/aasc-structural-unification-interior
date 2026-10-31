import OSRFrameSupply

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def restLength (w : SREvent) : ℝ := Real.sqrt (srOriginalOrderQuadratic w)

theorem rest_length_positive (w : SREvent) (future : IsFutureTimelike w) :
    0 < restLength w := Real.sqrt_pos.mpr future.2

theorem rest_length_square (w : SREvent) (future : IsFutureTimelike w) :
    (restLength w)^2=w.1^2-‖w.2‖^2 := by
  calc
    (restLength w)^2=srOriginalOrderQuadratic w := Real.sq_sqrt future.2.le
    _ = _ := sr_original_order_quadratic_computed w

def normalizedTangent (w : SREvent) : SREvent := (restLength w)⁻¹ • w

theorem normalized_tangent_is_future_unit (w : SREvent) (future : IsFutureTimelike w) :
    IsFutureUnit (normalizedTangent w) := by
  have positive := rest_length_positive w future
  refine ⟨mul_pos (inv_pos.mpr positive) future.1,?_⟩
  rw [sr_original_order_quadratic_computed]
  change ((restLength w)⁻¹*w.1)^2-‖(restLength w)⁻¹ • w.2‖^2=1
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos positive]
  have square := rest_length_square w future
  field_simp
  nlinarith

theorem rest_length_times_normalized_tangent (w : SREvent) (future : IsFutureTimelike w) :
    restLength w • normalizedTangent w=w := by
  unfold normalizedTangent
  rw [smul_smul,mul_inv_cancel₀ (rest_length_positive w future).ne',one_smul]

def outboundFrame (w : SREvent) (future : IsFutureTimelike w) : SRMatrixFrame :=
  suppliedUnitFrame (normalizedTangent w) (normalized_tangent_is_future_unit w future)

theorem outbound_frame_mem (w : SREvent) (future : IsFutureTimelike w) :
    outboundFrame w future ∈ srNativeFrameComparisons :=
  supplied_unit_frame_mem _ _

theorem outbound_frame_actual_interval (w : SREvent) (future : IsFutureTimelike w) :
    srMatrixFrameEventLinear (outboundFrame w future) (restLength w,0)=w := by
  have scale : (restLength w,(0:SRSpace)) = restLength w • ((1:ℝ),(0:SRSpace)) := by ext <;> simp
  rw [scale,map_smul]
  change restLength w • srMatrixFrameEventLinear
    (suppliedUnitFrame (normalizedTangent w) (normalized_tangent_is_future_unit w future)) (1,0)=w
  rw [supplied_unit_frame_rest]
  exact rest_length_times_normalized_tangent w future

def restFrame (w : SREvent) (future : IsFutureTimelike w) : SRMatrixFrame := (outboundFrame w future)⁻¹

theorem actual_rest_presentation (w : SREvent) (future : IsFutureTimelike w) :
    restFrame w future ∈ srNativeFrameComparisons ∧
      srMatrixFrameEventLinear (restFrame w future) w=(restLength w,0) := by
  refine ⟨srNativeFrameComparisons.inv_mem (outbound_frame_mem w future),?_⟩
  change srMatrixFrameEventLinear (outboundFrame w future)⁻¹ w=(restLength w,0)
  calc
    _ = srMatrixFrameEventLinear (outboundFrame w future)⁻¹
        (srMatrixFrameEventLinear (outboundFrame w future) (restLength w,0)) :=
      congrArg (srMatrixFrameEventLinear (outboundFrame w future)⁻¹) (outbound_frame_actual_interval w future).symm
    _ = _ := sr_event_frame_inverse_left _ _

end AASCKleinGordon.OperationalSR
