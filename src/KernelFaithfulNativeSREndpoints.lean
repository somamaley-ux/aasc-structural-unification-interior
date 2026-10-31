import SRLicensedFiniteProtocol
import SRConcreteMovingClock

/-! Bounded native flat/free/test-clock successor. The original-use constraints
incur Kernel roles; explicit downstream physical source data construct the form;
canonical licensing and the actual joint receiver connect the resulting uses to
the accepted EH/free-scalar receivers. No universal physical minimum is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open KGQuantum W9 TopologicalSpace
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

structure KernelFaithfulNativeSREndpoints : Prop where
  acceptedEndpoints : KernelFaithfulLicensedEndpoints a s Ω
  originalCoverage : Function.Surjective (presentJointOriginal a s Ω)
  exactDescent : ∀ op : JointOperation,
    ∃! reduced : JointReceiver a s Ω → Option (JointReceiver a s Ω),
      ∀ j, reduced (presentJointOriginal a s Ω j) =
        Option.map (presentJointOriginal a s Ω) (jointOperation a s Ω op j)
  exactFirstFailures : ∀ ops j,
    jointReceiverFirstFailure a s Ω ops (presentJointOriginal a s Ω j) =
      jointFirstFailure a s Ω ops j
  allOriginalRecords : ∀ j σ,
    ContextualQuotient.readCoordinate (jointCompleteObserve a s Ω) (.original (.inl σ))
      (presentJointOriginal a s Ω j) = srNativeCoastingMarkedRecord a.mass j.clock.record σ
  nativeTranslationAction :
    (∀ d e : SREvent, (∀ p : SREvent, p+d=p+e) → d=e) ∧
      (∀ p q : SREvent, ∃ d : SREvent, p+d=q)
  nativeNoDoubleIdentity : ∀ d : SREvent, d+d=0 → d=0
  nativeOneParameterTangent : ∀ v : SREvent, ∀ t : ℝ,
    HasDerivAt (srNativeTranslationOneParameter v) v t
  nativeSmoothOrbit : ∀ o v : SREvent,
    srNativeOriginalTranslationOrbitDiffeomorph o v = o+v ∧
      (srNativeOriginalTranslationOrbitDiffeomorph o).symm v = v-o
  originalAffine : ∀ (F : SREvent ≃ₜ SREvent)
    (normalizes : ∀ v : SREvent, ∃ w : SREvent, ∀ x : SREvent, F (x+v)=F x+w) z,
      F z = srMatrixFrameEventLinear (srOriginalFrameUnit F normalizes) z + F 0
  sourceConstructedGeometry : ∀ z : SREvent, srOriginalOrderQuadratic z = z.1^2-‖z.2‖^2
  sourceNondegenerate : srOriginalOrderQuadratic.associated.SeparatingLeft
  sourceFullCone : ∀ z : SREvent,
    z ∈ srRayFutureCone ↔ 0 ≤ z.1 ∧ 0 ≤ srOriginalOrderQuadratic z
  calibratedFrameDerivation : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame), A ∈ source.comparisons →
      srFramePullback (A : ComparisonMatrix) = comparisonUnitLorentz
  originalFrameGeometry : ∀ (source : SRCalibratedFrameSource a.mass)
    (F : SROriginalAdmittedFrame a.mass source) (x y : SREvent),
      srOriginalOrderQuadratic (F.eventMap y-F.eventMap x) = srOriginalOrderQuadratic (y-x)
  actualMovingFrame : srConcreteMovingBoost ∈ (srNativeOccupiedFrameSource a.mass a.mass_pos).comparisons ∧
    ((srConcreteMovingBoost : ComparisonMatrix).mulVec (originalComparisonProbe 0)) 1 = 3/4
  actualMovingClock :
    srNativeClockMass a.mass (srConcreteMovingClockState a.mass) = a.mass ∧
      srNativeClockHamiltonian a.mass (srConcreteMovingClockState a.mass) = a.mass*(5/4) ∧
      (srConcreteMovingClockState a.mass).momentum 0 = a.mass*(3/4) ∧
      srNativeClockRate a.mass (srConcreteMovingClockState a.mass) = 4/5
  actualClockMetricRate : ∀ z : SRNativeClockState SRSpace, 0 < srNativeClockMass a.mass z →
    Real.sqrt (srOriginalOrderQuadratic (1,srNativeClockVelocity a.mass z)) = srNativeClockRate a.mass z
  actualNormalizedIntervalCalibration : ∀ (x : SRSpace) (t u : ℝ),
    srConstructedNormalizedIntervalDuration (A:=ℝ) (u-t) =
      (srNativeClockCoastFlow a.mass u (srNativeRestClock x)).reading-
        (srNativeClockCoastFlow a.mass t (srNativeRestClock x)).reading
  originalSameEvent : ∀ (source : SRCalibratedFrameSource a.mass)
    (F : SROriginalAdmittedFrame a.mass source) (c : SRNativeClockUse SRSpace) σ,
    0 < srNativeClockMass a.mass c.record.2.2 →
      srMarkedClockEvent a.mass (srOriginalFrameClockUse F c).record
        ((F.eventMap (srMarkedClockEvent a.mass c.record σ)).1) =
          F.eventMap (srMarkedClockEvent a.mass c.record σ)
  originalClockEligibilityAndFailure : ∀ (source : SRCalibratedFrameSource a.mass)
    (F : SROriginalAdmittedFrame a.mass source) (c : SRNativeClockUse SRSpace),
    (srNativeClockUseValid a.mass (srOriginalFrameClockUse F c) ↔ srNativeClockUseValid a.mass c) ∧
      srClockCertification a.mass (srOriginalFrameClockUse F c) = srClockCertification a.mass c
  finitePulseLegs : ∀ (source : SRCalibratedFrameSource a.mass)
    (F : SROriginalAdmittedFrame a.mass source) (l : ℝ), 0 < l →
    ∀ n : SRSpace, ‖n‖=1 → ∀ N : ℕ, ∀ k : Fin N,
      F.eventMap (srNativeProtocolReflection l n k.val)-F.eventMap (srNativeProtocolDeparture l k.val)
        ∈ srOriginalFutureRayIncrements ∧
      F.eventMap (srNativeProtocolReturn l k.val)-F.eventMap (srNativeProtocolReflection l n k.val)
        ∈ srOriginalFutureRayIncrements
  nativeProtocolOccupation : ∀ (l ε : ℝ), 0 < l → 0 < ε →
    ∀ n : SRSpace, ‖n‖=1 → ∀ N : ℕ,
    (0 < srNativeClockMass a.mass (srNativeRestClock (0:SRSpace))) ∧
    (0 < srNativeClockMass a.mass (srNativeRestClock (l • n))) ∧
    (∀ k : Fin N,
      srNativeProtocolReflection l n k.val-srNativeProtocolDeparture (E:=SRSpace) l k.val ∈ srOriginalFutureRayIncrements ∧
      srNativeProtocolReturn (E:=SRSpace) l k.val-srNativeProtocolReflection l n k.val ∈ srOriginalFutureRayIncrements ∧
      (srNativeClockCoastFlow a.mass (srNativeProtocolReturn (E:=SRSpace) l k.val).1 (srNativeRestClock (0:SRSpace))).reading =
        2*((k.val:ℝ)+1)*l) ∧ srNativePositiveRayMomentum ε n ∈ srOriginalFutureRayIncrements
  finitePulseReadouts : ∀ (source : SRCalibratedFrameSource a.mass)
    (F : SROriginalAdmittedFrame a.mass source) (l : ℝ) (N : ℕ) (k : Fin N),
    (srNativeCoastingMarkedRecord a.mass
      (srPassiveClockRecord a.mass (srOriginalFrameUnit F.eventMap F.normalizesOriginalTranslations)
        (F.eventMap 0) (0,0,srNativeRestClock 0))
      ((F.eventMap (srMarkedClockEvent a.mass (0,0,srNativeRestClock 0)
        (srNativeProtocolReturn (E:=SRSpace) l k.val).1)).1)).2.reading = 2*((k.val:ℝ)+1)*l
  canonicalKernelAndLicense :
    let D := originalJointSRTask a s Ω
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧ FiveLicensingConclusions D ∧
      (∀ x, srNativeClockUseValid a.mass x.clock →
        constructedLicensing D x (originalJointSRUseMeaning a s Ω))
  licensedValidSource : ∀ r : LicensedJointSRReceiver a s Ω,
    srNativeClockUseValid a.mass (licensedJointSRSource a s Ω r).clock
  licensedCoverage : ∀ (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    ∃ j : LicensedJointSRReceiver a s Ω,
      licensedSRScalar a s Ω j = r ∧ (licensedJointSRSource a s Ω j).metric = H
  licensedFiniteProtocolSource : ∀ l (length : 0 < l) N
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    licensedJointSRSource a s Ω (licensedJointFiniteProtocol a s Ω l length N r H) =
      jointFiniteProtocolSource a s Ω l N r H
  licensedFiniteProtocolReceipt : ∀ l (length : 0 < l) N
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    srClockCertification a.mass
      (licensedJointSRSource a s Ω (licensedJointFiniteProtocol a s Ω l length N r H)).clock = some (2*(N:ℝ)*l)
  licensedFiniteProtocolSameEvent : ∀ (source : SRCalibratedFrameSource a.mass)
    (F : SROriginalAdmittedFrame a.mass source) l (length : 0 < l) N
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) (k : Fin N),
    let receiver := licensedJointFiniteProtocol a s Ω l length N r H
    let moved := licensedSRPassiveFrame a s Ω source
      (srOriginalFrameUnit F.eventMap F.normalizesOriginalTranslations) F.admitted (F.eventMap 0) receiver
    (srNativeCoastingMarkedRecord a.mass (licensedJointSRSource a s Ω moved).clock.record
      ((F.eventMap (srMarkedClockEvent a.mass (licensedJointSRSource a s Ω receiver).clock.record
        (srNativeProtocolReturn (E:=SRSpace) l k.val).1)).1)).2.reading = 2*((k.val:ℝ)+1)*l
  licensedPassiveActualSource : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) b (r : LicensedJointSRReceiver a s Ω),
    licensedJointSRSource a s Ω (licensedSRPassiveFrame a s Ω source A ha b r) =
      jointPassiveFrame a s Ω A b (licensedJointSRSource a s Ω r)
  licensedFrameComposition : ∀ (source : SRCalibratedFrameSource a.mass)
    (A B : SRMatrixFrame) (ha : A ∈ source.comparisons) (hb : B ∈ source.comparisons)
    bA bB (r : LicensedJointSRReceiver a s Ω),
    licensedSRPassiveFrame a s Ω source A ha bA (licensedSRPassiveFrame a s Ω source B hb bB r) =
      licensedSRPassiveFrame a s Ω source (A*B) (source.comparisons.mul_mem ha hb)
        (srMatrixFrameEventLinear A bB+bA) r
  licensedFrameIdentity : ∀ (source : SRCalibratedFrameSource a.mass) (r : LicensedJointSRReceiver a s Ω),
    licensedSRPassiveFrame a s Ω source 1 source.comparisons.one_mem 0 r = r
  licensedFrameInverse : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) b (r : LicensedJointSRReceiver a s Ω),
    licensedSRPassiveFrame a s Ω source A⁻¹ (source.comparisons.inv_mem ha)
      (-srMatrixFrameEventLinear A⁻¹ b) (licensedSRPassiveFrame a s Ω source A ha b r) = r
  licensedScalarFrameNaturality : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) b t (r : LicensedJointSRReceiver a s Ω),
    licensedJointSRContinue a s Ω (.inl t) (licensedSRPassiveFrame a s Ω source A ha b r) =
      licensedSRPassiveFrame a s Ω source A ha b (licensedJointSRContinue a s Ω (.inl t) r)
  licensedClockFrameNaturality : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (ha : A ∈ source.comparisons) b
    (δ : {δ : ℝ // 0 ≤ δ}) (r : LicensedJointSRReceiver a s Ω),
    licensedSRPassiveFrame a s Ω source A ha b (licensedJointSRContinue a s Ω (.inr δ) r) =
      licensedJointSRContinue a s Ω
        (.inr ⟨srPassiveClockSlope a.mass A (licensedJointSRSource a s Ω r).clock.record.2.2*δ.val,
          mul_nonneg (sr_passive_clock_slope_positive a.mass source A ha _
            (licensed_joint_sr_has_actual_valid_source a s Ω r).1).le δ.property⟩)
        (licensedSRPassiveFrame a s Ω source A ha b r)
  licensedClockActualReadout : ∀ (δ : {δ : ℝ // 0 ≤ δ}) (r : LicensedJointSRReceiver a s Ω),
    srNativeClockActualInterval a.mass
      (licensedJointSRSource a s Ω (licensedJointSRContinue a s Ω (.inr δ) r)).clock =
        srNativeClockActualInterval a.mass (licensedJointSRSource a s Ω r).clock +
          δ.val * srNativeClockRate a.mass (licensedJointSRSource a s Ω r).clock.record.2.2
  exactOperationTransport : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (_ha : A ∈ source.comparisons) b op (j : JointOriginalSource a s Ω),
    0 < srNativeClockMass a.mass j.clock.record.2.2 →
    jointOperation a s Ω (transportJointOperation (srPassiveClockSlope a.mass A j.clock.record.2.2) op)
      (jointPassiveFrame a s Ω A b j) =
        (jointOperation a s Ω op j).map (jointPassiveFrame a s Ω A b)
  finiteFailureTransport : ∀ (source : SRCalibratedFrameSource a.mass)
    (A : SRMatrixFrame) (_ha : A ∈ source.comparisons) b ops (j : JointOriginalSource a s Ω),
    0 < srNativeClockMass a.mass j.clock.record.2.2 →
    jointFirstFailure a s Ω (ops.map (transportJointOperation
      (srPassiveClockSlope a.mass A j.clock.record.2.2))) (jointPassiveFrame a s Ω A b j) =
        jointFirstFailure a s Ω ops j
  sameMetricOperand : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0) (j : LicensedJointSRReceiver a s Ω),
    restrictedEHMetric a s Ω (licensedEHResponse a s Ω (licensedSRMetric a s Ω κ Λ coupling j)) =
      originalEHActMetric (licensedJointSRSource a s Ω j).metric.val
  sameOriginalPreparation : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0) (j : LicensedJointSRReceiver a s Ω),
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω (licensedSRMetric a s Ω κ Λ coupling j))) =
      rayMap _ (licensedScalarOriginalPure a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω j))
  sameRegisteredReferences : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0) (j : LicensedJointSRReceiver a s Ω)
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))),
    (licensedReadout a s Ω (licensedSRMetric a s Ω κ Λ coupling j) []).answer
      (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q)) =
        (licensedScalarReference a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω j)
          (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr
  evolvedOriginalPreparation : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0) t (r : LicensedJointSRReceiver a s Ω),
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (licensedSRMetric a s Ω κ Λ coupling (licensedJointSRContinue a s Ω (.inl t) r)))) =
      rayMap _ (kgNRSpatialOriginalPreparation a t
        (licensedScalarPure a s Ω (scalarBaseObject a) (licensedSRScalar a s Ω r)))
  actualFlatEHIdentification : ∀ (p : CoordinatePoint) (z : SREvent),
    comparisonQuadratic (originalEHActMetric (0 : MetricSourceProbe Ω) p) (srEventCoordinates z) =
      -srOriginalOrderQuadratic z

theorem kernel_faithful_native_sr_canonical_licensing_eh_scalar : KernelFaithfulNativeSREndpoints a s Ω := by
  refine {
    acceptedEndpoints := kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger a s Ω
    originalCoverage := joint_original_receiver_coverage a s Ω
    exactDescent := joint_registered_operations_have_unique_exact_descent a s Ω
    exactFirstFailures := joint_first_failure_square a s Ω
    allOriginalRecords := joint_all_marked_clock_records_recovered a s Ω
    nativeTranslationAction := sr_native_whole_translation_event_action_free_and_transitive
    nativeNoDoubleIdentity := sr_native_whole_translation_comparison_has_no_double_identity
    nativeOneParameterTangent := sr_native_translation_one_parameter_actual_tangent
    nativeSmoothOrbit := sr_native_bundled_orbit_retains_actual_original_translation
    originalAffine := sr_original_event_frame_is_constructed_affine
    sourceConstructedGeometry := sr_original_order_quadratic_computed
    sourceNondegenerate := ?_
    sourceFullCone := ?_
    calibratedFrameDerivation := sr_original_source_calibrated_frames_preserve_constructed_metric a.mass a.mass_pos
    originalFrameGeometry := sr_original_admitted_frame_metric_displacement_square a.mass a.mass_pos
    actualMovingFrame := sr_native_comparison_family_contains_genuine_moving_frame
    actualMovingClock := sr_native_actual_moving_clock_energy_momentum_and_rate a.mass a.mass_pos
    actualClockMetricRate := ?_
    actualNormalizedIntervalCalibration := sr_original_real_interval_calibration_equals_actual_rest_clock_receipt a.mass a.mass_pos
    originalSameEvent := sr_original_admitted_frame_transports_actual_clock_event a.mass a.mass_pos
    originalClockEligibilityAndFailure := sr_original_admitted_frame_preserves_clock_use_and_failure a.mass a.mass_pos
    finitePulseLegs := sr_every_finite_original_pulse_protocol_has_frame_natural_legs a.mass
    nativeProtocolOccupation := fun l ε length energy n unit N =>
      sr_native_every_finite_roundtrip_has_same_source_clock_and_ray_records a.mass l ε a.mass_pos length energy n unit N
    finitePulseReadouts := sr_every_finite_original_return_tick_has_same_source_frame_reading a.mass a.mass_pos
    canonicalKernelAndLicense := joint_sr_use_constructs_kernel_and_canonical_license a s Ω
    licensedValidSource := licensed_joint_sr_has_actual_valid_source a s Ω
    licensedCoverage := licensed_sr_covers_every_scalar_and_metric_preparation a s Ω
    licensedFiniteProtocolSource := licensed_finite_protocol_source_square a s Ω
    licensedFiniteProtocolReceipt := licensed_finite_protocol_actual_clock_receipt a s Ω
    licensedFiniteProtocolSameEvent := licensed_finite_protocol_every_same_event_return_reading a s Ω
    licensedPassiveActualSource := by intros; rfl
    licensedFrameComposition := licensed_sr_passive_frame_composition a s Ω
    licensedFrameIdentity := licensed_sr_passive_frame_identity a s Ω
    licensedFrameInverse := licensed_sr_passive_frame_inverse a s Ω
    licensedScalarFrameNaturality := licensed_sr_scalar_evolution_frame_naturality a s Ω
    licensedClockFrameNaturality := licensed_sr_clock_extension_frame_naturality a s Ω
    licensedClockActualReadout := licensed_joint_sr_clock_continuation_adds_actual_readout a s Ω
    exactOperationTransport := joint_passive_registered_operation_square a s Ω
    finiteFailureTransport := joint_passive_every_finite_first_failure_square a s Ω
    sameMetricOperand := licensed_sr_same_metric_operand_square a s Ω
    sameOriginalPreparation := licensed_sr_same_original_preparation_square a s Ω
    sameRegisteredReferences := licensed_sr_complete_registered_reference_square a s Ω
    evolvedOriginalPreparation := licensed_joint_sr_evolved_original_preparation_square a s Ω
    actualFlatEHIdentification := sr_source_derived_form_matches_actual_zero_eh_operand }
  · exact sr_completed_order_constructed_lorentz_form_nondegenerate
      (srRayClock (E:=SRSpace)) (srRayRestVector (E:=SRSpace))
      (sr_ray_rest_clock_one (E:=SRSpace)) (srNativeOrientedCompletedOrderSource (E:=SRSpace) (by simp))
  · intro z
    rw [sr_original_order_quadratic_computed]
    change ‖z.2‖ ≤ z.1 ↔ 0 ≤ z.1 ∧ 0 ≤ z.1^2-‖z.2‖^2
    constructor
    · intro h
      have ht := (norm_nonneg z.2).trans h
      exact ⟨ht,by nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg ht (norm_nonneg z.2))]⟩
    · rintro ⟨ht,hq⟩
      nlinarith [norm_nonneg z.2]
  · intro z positive
    exact sr_native_actual_clock_rate_is_positive_metric_root (by simp) a.mass z positive

#print axioms kernel_faithful_native_sr_canonical_licensing_eh_scalar
end AASCKleinGordon.CanonicalLicensing.SRIntegration
