import OSRIdealResponse
import OSRDirectionalClocks
import OSRTimelikeComparison
import OSRClockFrameTransport

/-! An occupied uniform-response class. Its duration is computed from the
actual Hamiltonian reading; the square-root identity is proved afterward. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
attribute [local instance] Classical.propDecidable

def nativeDuration (mu0 J : ℝ) (w : SREvent) : ℝ :=
  if IsFutureTimelike w then
    (srNativeClockCoastFlow mu0 w.1 (directionalClock mu0 J (normalizedTangent w) 0 0)).reading-
      (directionalClock mu0 J (normalizedTangent w) 0 0).reading
  else 0

theorem native_duration_zero (mu0 J : ℝ) : nativeDuration mu0 J 0=0 := by
  simp [nativeDuration,IsFutureTimelike]

theorem native_duration_is_actual_metric_length (mu0 J : ℝ) (positive : 0 < mu0+J)
    (w : SREvent) (future : IsFutureTimelike w) : nativeDuration mu0 J w=restLength w := by
  rw [nativeDuration,if_pos future]
  change (srNativeClockCoastFlow mu0 w.1 (directionalClock mu0 J (normalizedTangent w) 0 0)).reading-0=restLength w
  rw [sub_zero]
  have time : restLength w*(normalizedTangent w).1=w.1 := by
    change restLength w*((restLength w)⁻¹*w.1)=w.1
    field_simp [(rest_length_positive w future).ne']
  have reading := directional_clock_actual_reading mu0 J positive (normalizedTangent w)
    (normalized_tangent_is_future_unit w future) 0 0 (restLength w)
  rw [time,zero_add] at reading
  exact reading

theorem native_duration_unit_scale (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (t : ℝ) (forward : 0 ≤ t) :
    nativeDuration mu0 J (t • U)=t := by
  by_cases zero : t=0
  · subst t
    simp [native_duration_zero]
  · rw [native_duration_is_actual_metric_length mu0 J positive _
      (future_unit_positive_scale U unit t (lt_of_le_of_ne forward (Ne.symm zero))),
      future_unit_scaled_rest_length U unit t forward]

def nativeCertified : Set SREvent := {w | w=0 ∨ IsFutureTimelike w}

theorem native_certified_frame (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons) (w : SREvent) :
    w ∈ nativeCertified ↔ srMatrixFrameEventLinear A w ∈ nativeCertified := by
  constructor
  · rintro (zero | future)
    · left
      rw [zero,map_zero]
    · exact Or.inr (native_frame_preserves_future_timelike A admitted w future)
  · rintro (zero | future)
    · left
      exact (srMatrixFrameEventLinear A).injective (zero.trans (map_zero _).symm)
    · exact Or.inr ((native_frame_future_timelike_iff A admitted w).mpr future)

theorem native_duration_same_event_frame (mu0 J : ℝ) (positive : 0 < mu0+J)
    (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons) (w : SREvent) (inside : w ∈ nativeCertified) :
    nativeDuration mu0 J (srMatrixFrameEventLinear A w)=nativeDuration mu0 J w := by
  rcases inside with zero | future
  · rw [zero,map_zero]
  · rw [native_duration_is_actual_metric_length mu0 J positive w future,
      native_duration_is_actual_metric_length mu0 J positive _ (native_frame_preserves_future_timelike A admitted w future)]
    unfold restLength
    rw [native_frame_source_quadratic A admitted]

def nativeIdealResponse (mu0 J : ℝ) (_base : 0 < mu0) (positive : 0 < mu0+J) : IdealInertialResponse where
  certified := nativeCertified
  zero_certified := Or.inl rfl
  future_domain := fun _ h => h
  duration := nativeDuration mu0 J
  positive_readout := by
    intro w _ future
    rw [native_duration_is_actual_metric_length mu0 J positive w future]
    exact rest_length_positive w future
  ray_subdivision := by
    intro U unit T _ _ t ht _
    by_cases zero : t=0
    · left
      simp [zero]
    · exact Or.inr (future_unit_positive_scale U unit t (lt_of_le_of_ne ht (Ne.symm zero)))
  ray_addition := by
    intro U unit t s ht hs _
    rw [native_duration_unit_scale mu0 J positive U unit (t+s) (add_nonneg ht hs),
      native_duration_unit_scale mu0 J positive U unit t ht,native_duration_unit_scale mu0 J positive U unit s hs]
  comparison_available := fun _ _ => True
  comparison_certified := fun A admitted w inside _ => (native_certified_frame A admitted w).mp inside
  same_event_readout := fun A admitted w inside _ => native_duration_same_event_frame mu0 J positive A admitted w inside
  rest_coverage := by
    intro w _ future
    have presentation := actual_rest_presentation w future
    refine ⟨restFrame w future,presentation.1,True.intro,?_⟩
    exact congrArg Prod.snd presentation.2
  rest_span := 1
  rest_span_positive := by norm_num
  rest_span_certified := by
    right
    refine ⟨by norm_num,?_⟩
    rw [sr_original_order_quadratic_computed]
    norm_num
  rest_calibration := by
    simpa using native_duration_unit_scale mu0 J positive (1,0) rest_unit_is_future_unit 1 (by norm_num)

def nativeIntervalUse (mu0 J : ℝ) (w : SREvent) : SRNativeClockUse SRSpace :=
  directionalClockUse mu0 J (normalizedTangent w) 0 0 (restLength w)

theorem native_duration_has_actual_original_use (mu0 J : ℝ) (positive : 0 < mu0+J)
    (w : SREvent) (future : IsFutureTimelike w) :
    srNativeClockUseValid mu0 (nativeIntervalUse mu0 J w) ∧
      srNativeClockActualInterval mu0 (nativeIntervalUse mu0 J w)=nativeDuration mu0 J w ∧
      srMarkedClockEvent mu0 (nativeIntervalUse mu0 J w).record (nativeIntervalUse mu0 J w).finish=w := by
  have unit := normalized_tangent_is_future_unit w future
  refine ⟨directional_clock_use_actually_valid mu0 J positive _ unit 0 0 _
    (rest_length_positive w future).le,?_,?_⟩
  · rw [native_duration_is_actual_metric_length mu0 J positive w future]
    exact directional_clock_use_actual_interval mu0 J positive _ unit 0 0 _
  · have event := directional_clock_actual_event mu0 J positive _ unit (0:SRSpace) 0 0 (restLength w)
    rw [show ((0:ℝ),(0:SRSpace))=(0:SREvent) from rfl,zero_add] at event
    simp only [zero_add] at event
    have final := event.trans (rest_length_times_normalized_tangent w future)
    simpa only [nativeIntervalUse,directionalClockUse,srMarkedClockEvent,srNativeCoastingMarkedRecord,
      Prod.fst_zero,Prod.snd_zero,zero_add,sub_zero] using final

theorem native_interval_use_is_same_passively_transported_clock (mu0 J : ℝ)
    (positive : 0 < mu0+J) (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) (future : IsFutureTimelike w) :
    nativeIntervalUse mu0 J (srMatrixFrameEventLinear A w)=
      srPassiveClockUse mu0 A 0 (nativeIntervalUse mu0 J w) := by
  unfold nativeIntervalUse
  rw [directional_clock_actual_passive_use mu0 J positive _
    (normalized_tangent_is_future_unit w future) 0 0 0 _ A]
  rw [rest_length_native_frame A admitted,normalized_tangent_native_frame A admitted]
  simp [frameEvent]

end AASCKleinGordon.OperationalSR
