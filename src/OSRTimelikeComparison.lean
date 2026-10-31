import OSRRestPresentation
import OSRAffineFrames

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

theorem actual_source_form_smul (t : ℝ) (w : SREvent) :
    srOriginalOrderQuadratic (t • w)=t^2*srOriginalOrderQuadratic w := by
  rw [sr_original_order_quadratic_computed,sr_original_order_quadratic_computed]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem actual_source_form_zero : srOriginalOrderQuadratic (0:SREvent)=0 := by
  rw [sr_original_order_quadratic_computed]
  norm_num

theorem native_frame_source_quadratic (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) : srOriginalOrderQuadratic (srMatrixFrameEventLinear A w)=srOriginalOrderQuadratic w := by
  rw [sr_original_order_quadratic_computed,sr_original_order_quadratic_computed]
  exact sr_source_form_isometry_event_value A admitted.1 w

theorem future_timelike_strict_cone (w : SREvent) (future : IsFutureTimelike w) : ‖w.2‖ < w.1 := by
  have positive := future.2
  rw [sr_original_order_quadratic_computed] at positive
  nlinarith [norm_nonneg w.2,future.1]

theorem native_frame_preserves_future_timelike (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) (future : IsFutureTimelike w) : IsFutureTimelike (srMatrixFrameEventLinear A w) := by
  have strict := sr_exact_original_cone_frame_preserves_strict_clock_body
    (srMatrixFrameEvent A) admitted.2.2 w (future_timelike_strict_cone w future)
  refine ⟨lt_of_le_of_lt (norm_nonneg _) strict,?_⟩
  rw [native_frame_source_quadratic A admitted]
  exact future.2

theorem native_frame_future_timelike_iff (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) : IsFutureTimelike w ↔ IsFutureTimelike (srMatrixFrameEventLinear A w) := by
  constructor
  · exact native_frame_preserves_future_timelike A admitted w
  · intro future
    have original := native_frame_preserves_future_timelike A⁻¹
      (srNativeFrameComparisons.inv_mem admitted) (srMatrixFrameEventLinear A w) future
    rwa [sr_event_frame_inverse_left] at original

theorem future_unit_positive_scale (U : SREvent) (unit : IsFutureUnit U) (t : ℝ) (positive : 0 < t) :
    IsFutureTimelike (t • U) := by
  refine ⟨mul_pos positive unit.1,?_⟩
  rw [actual_source_form_smul,unit.2,mul_one]
  exact sq_pos_of_pos positive

theorem future_unit_scaled_rest_length (U : SREvent) (unit : IsFutureUnit U) (t : ℝ) (positive : 0 ≤ t) :
    restLength (t • U)=t := by
  unfold restLength
  rw [actual_source_form_smul,unit.2,mul_one,Real.sqrt_sq positive]

theorem native_rest_time_is_actual_length (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) (w : SREvent) (future : IsFutureTimelike w)
    (atRest : (srMatrixFrameEventLinear A w).2=0) :
    srMatrixFrameEventLinear A w=(restLength w,0) := by
  have positive := (native_frame_preserves_future_timelike A admitted w future).1
  have square := native_frame_source_quadratic A admitted w
  rw [sr_original_order_quadratic_computed,atRest,norm_zero,zero_pow (by norm_num),sub_zero] at square
  apply Prod.ext
  · change (srMatrixFrameEventLinear A w).1=Real.sqrt (srOriginalOrderQuadratic w)
    rw [←square,Real.sqrt_sq positive.le]
  · exact atRest

theorem rest_length_native_frame (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) : restLength (srMatrixFrameEventLinear A w)=restLength w := by
  unfold restLength
  rw [native_frame_source_quadratic A admitted]

theorem normalized_tangent_native_frame (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) : normalizedTangent (srMatrixFrameEventLinear A w)=
      srMatrixFrameEventLinear A (normalizedTangent w) := by
  unfold normalizedTangent
  rw [rest_length_native_frame A admitted,map_smul]

end AASCKleinGordon.OperationalSR
