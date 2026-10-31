import KGCommonLicensedEvolution
import KGLicensedScalarEndpoint

/-! Constraint-first composed receipts for the declared original source and
its two current licensed receiving endpoints. Every field below is the exact
type of a proved semantic map, coverage, licensing or analytic receipt.

The shared preparation is the declared invariant one-particle core with an
independently admitted metric operand. EH history append and scalar NR time
flow remain distinct. This does not select a metric, assert matter matching,
exhaust the entire original role architecture, or remove the explicitly
quantified comparator calibration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace MeasureTheory CategoryTheory
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open scoped SchwartzMap
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KernelFaithfulLicensedEndpoints (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) : Prop where
  constraint_first_source : KGSpecificStandingSource a s Ω
  current_free_receiving : KGNRReceivingQS a s Ω
  geometric_einstein_receiving : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0),
    (∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧
      CoordinateEinsteinResponseForm (originalEHGeometricResponse κ Λ) ac.1 ac.2)

  receipt_current_metric_use_constructs_kernel_and_canonical_license : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0),
    let D := originalMetricTask a s Ω κ Λ
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧
    FiveLicensingConclusions D ∧
    (∀ h, constructedLicensing D h (originalMetricUseMeaning a s Ω κ Λ))

  receipt_receiver_has_actual_canonical_license : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ),
    constructedLicensing (originalMetricTask a s Ω κ Λ) (licensedHistory a s Ω r)
      (originalMetricUseMeaning a s Ω κ Λ)

  receipt_present_licensed_history_surjective : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0),
    Function.Surjective (presentLicensedHistory a s Ω κ Λ coupling)

  receipt_licensed_readout_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (ops : List (PreparedHistoryOperation a Ω)),
    licensedReadout a s Ω r ops = rawMetricUseProfile a s Ω κ Λ (licensedHistory a s Ω r) ops

  receipt_licensed_response_coverage : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0),
    Function.Surjective (licensedEHResponse a s Ω (κ := κ) (Λ := Λ))

  receipt_licensed_source_profile_coverage : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0),
    Function.Surjective (licensedEHSourceProfile a s Ω (κ := κ) (Λ := Λ))

  receipt_licensed_response_continuation_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (ops : List (PreparedHistoryOperation a Ω)) (r : LicensedMetricReceiver a s Ω κ Λ),
    licensedEHResponse a s Ω (licensedContinue a s Ω κ Λ coupling ops r) =
      restrictedOriginalResponseContinue a s Ω ops (licensedEHResponse a s Ω r)

  receipt_licensed_readout_continuation_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (first second : List (PreparedHistoryOperation a Ω)) (r : LicensedMetricReceiver a s Ω κ Λ),
    licensedReadout a s Ω (licensedContinue a s Ω κ Λ coupling first r) second =
      licensedReadout a s Ω r (first ++ second)

  receipt_licensed_metric_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ),
    (licensedReadout a s Ω r []).metric = restrictedEHMetric a s Ω (licensedEHResponse a s Ω r)

  receipt_licensed_action_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ),
    (licensedReadout a s Ω r []).finiteAction =
      originalEHRelativeAction κ Λ wickNativeFlatMetric (restrictedEHAct a s Ω (licensedEHResponse a s Ω r)).val

  receipt_licensed_directional_action_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (K : MetricSourceProbe Ω),
    (licensedReadout a s Ω r []).directionalAction K =
      restrictedEHObserve a s Ω κ Λ (licensedEHResponse a s Ω r) K

  receipt_licensed_original_answer_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (q : PreparedQuestion a Ω),
    (licensedReadout a s Ω r []).answer q =
      preparedHistoryReference a s Ω (restrictedOriginalResponseReceive a s Ω (licensedEHResponse a s Ω r)) q

  receipt_licensed_original_first_failure_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ),
    (licensedReadout a s Ω r []).firstFailure =
      preparedHistoryReadFirstFailure a s Ω
        (restrictedOriginalResponseReceive a s Ω (licensedEHResponse a s Ω r))

  receipt_licensed_eh_source_is_original_directional_action : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (K : MetricSourceProbe Ω),
    (1 / 2 : ℝ) * metricSourcePairing
      (restrictedEHKernelSource a s Ω κ Λ coupling (licensedEHSourceProfile a s Ω r)) K =
        (licensedReadout a s Ω r []).directionalAction K

  receipt_licensed_eh_same_metric_representation : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (i : Fin 10) (φ : ScalarSourceProbe Ω),
    restrictedEHKernelSource a s Ω κ Λ coupling (licensedEHSourceProfile a s Ω r) i φ =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (licensedReadout a s Ω r []).metric
        (originalEHGeometricResponse κ Λ (licensedReadout a s Ω r []).metric)) i p * φ p

  receipt_licensed_original_failure_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (q : PreparedQuestion a Ω),
    (licensedReadout a s Ω r []).failure q =
      preparedEventFailure a s Ω
        ⟨restrictedEHPrepared a s Ω (licensedEHResponse a s Ω r), q⟩

  receipt_licensed_rejected_metric_request_stays_failed : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (H : MetricSourceProbe Ω)
    (rejected : H ∉ wickOriginalMetricNeighborhood Ω),
    (licensedReadout a s Ω r []).failure (preparedFiniteRequest a Ω H) =
      some KGExecutionFailure.originalMetricRejection

  receipt_scalar_use_constructs_kernel_and_canonical_license : ∀ (A : KGNRObject a),
    let D := originalScalarTask a s Ω A
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧ FiveLicensingConclusions D ∧
    (∀ x, constructedLicensing D x (originalScalarUseMeaning a s Ω A))

  receipt_every_original_scalar_has_canonical_license : ∀ (A : KGNRObject a) (x : PureVector (KGNRCarrier A)),
    constructedLicensing (originalScalarTask a s Ω A) x (originalScalarUseMeaning a s Ω A)

  receipt_present_licensed_scalar_surjective : ∀ (A : KGNRObject a),
    Function.Surjective (presentLicensedScalar a s Ω A)

  receipt_licensed_scalar_meaning_exact : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A),
    licensedScalarMeaning a s Ω A r = originalScalarUseMeaning a s Ω A

  receipt_licensed_scalar_state_coverage : ∀ (A : KGNRObject a),
    Function.Surjective (licensedScalarState a s Ω A)

  receipt_licensed_scalar_old_reference_square : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    (q : RegisteredQuestion (KGFamilyQuestion a Ω A.raw)),
    licensedScalarReference a s Ω A r (mapRegisteredQuestion kgNROldQuestion q) =
      (kgRawRegisteredOrbit a s Ω A.raw).references.referenceAt (licensedScalarOriginalPure a s Ω A r) q

  receipt_licensed_scalar_old_complete_record : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    (q : KGFamilyQuestion a Ω A.raw),
    licensedScalarOutput a s Ω A r (kgNROldQuestion q) =
      kgFamilyOutput a s Ω A.raw (licensedScalarOriginalPure a s Ω A r) q

  receipt_licensed_scalar_continuation_reference : ∀ (A : KGNRObject a) (t : ℝ) (r : LicensedScalarReceiver a s Ω A)
    (q : ScalarUseQuestion a Ω A),
    licensedScalarReference a s Ω A (licensedScalarContinue a s Ω A t r) q =
      licensedScalarReference a s Ω A r (mapRegisteredQuestion (kgNRQuestionAdvance t) q)

  receipt_licensed_scalar_continuation_first_failure : ∀ (A : KGNRObject a) (t : ℝ) (r : LicensedScalarReceiver a s Ω A)
    (word : List (KGNRReceivingQuestion a Ω A.shape)),
    kgFirstFailure (licensedScalarOutput a s Ω A r) (word.map (kgNRQuestionAdvance t)) =
      kgFirstFailure (licensedScalarOutput a s Ω A (licensedScalarContinue a s Ω A t r)) word

  receipt_licensed_scalar_full_continuation_square : ∀ (A : KGNRObject a) (t : ℝ) (r : LicensedScalarReceiver a s Ω A),
    licensedScalarFullState a s Ω A (licensedScalarContinue a s Ω A t r) =
      unitaryRayMap (kgNRFullFamilyFlow a t A.shape) (licensedScalarFullState a s Ω A r)

  receipt_licensed_scalar_comparison_reference : ∀ (A : KGNRObject a) {B : KGNRObject a} (f : A ⟶ B)
    (r : LicensedScalarReceiver a s Ω A) (q : ScalarUseQuestion a Ω B),
    licensedScalarReference a s Ω A r (mapRegisteredQuestion (kgNRQuestionPullback f.lift) q) =
      licensedScalarReference a s Ω B (licensedScalarComparison a s Ω A f r) q

  receipt_licensed_scalar_region_reference : ∀ (A : KGNRObject a) {V : Opens CoordinatePoint} (h : Ω ≤ V)
    (r : LicensedScalarReceiver a s Ω A) (q : ScalarUseQuestion a Ω A),
    licensedScalarReference a s V A (licensedScalarRegion a s Ω A h r)
      (mapRegisteredQuestion (kgNRQuestionExtend h) q) = licensedScalarReference a s Ω A r q

  receipt_licensed_scalar_tensor_original_square : ∀ (A : KGNRObject a) (B : KGNRObject a)
    (r : LicensedScalarReceiver a s Ω A) (t : LicensedScalarReceiver a s Ω B),
    licensedScalarOriginalPure a s Ω (kgNRTensor A B) (licensedScalarTensor a s Ω A B r t) =
      kgRawTensor (licensedScalarOriginalPure a s Ω A r) (licensedScalarOriginalPure a s Ω B t)

  receipt_licensed_scalar_domain_graph_receipt : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A),
    (↑(licensedScalarHamiltonian a s Ω A r).domain : Set KGNRSpatialHilbert) =
      (licensedScalarMeaning a s Ω A r).fullKineticDomain ∧
    (↑(licensedScalarHamiltonian a s Ω A r).graph : Set (KGNRSpatialHilbert × KGNRSpatialHilbert)) =
      (licensedScalarMeaning a s Ω A r).fullKineticGraph

  receipt_licensed_scalar_full_flow_receipt : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    (t : ℝ) (f : KGNRSpatialHilbert),
    licensedScalarFullFlow a s Ω A r t f = (licensedScalarMeaning a s Ω A r).fullScalarEvolution t f

  receipt_licensed_scalar_exact_generator : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A),
    GlobalCharge.ExactGenerator (Translation.coefficient (licensedScalarMeaning a s Ω A r).parameters.hbar)
      (licensedScalarFullFlow a s Ω A r) (licensedScalarHamiltonian a s Ω A r)

  receipt_licensed_scalar_complete_weak_graph : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    (f g : KGNRSpatialHilbert),
    (f, g) ∈ (licensedScalarHamiltonian a s Ω A r).graph ↔
      ∀ test : 𝓢(KGSpatialSpace, ℂ), (g : KGSpatialDistribution) test =
        (f : KGSpatialDistribution) (kgNRSpatialTestResponse a test)

  receipt_licensed_scalar_calibrated_comparator : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    {H : LinearPMap ℂ KGNRSpatialHilbert KGNRSpatialHilbert} (C : KGScalarFreeComparator H)
    (calibration : KGFreeAnchoredDispersionAt a C),
    H = licensedScalarHamiltonian a s Ω A r

  receipt_licensed_scalar_free_ssq1 : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A),
    SameScopeQuantumSpatial1 (licensedScalarMeaning a s Ω A r).parameters
      (licensedScalarHamiltonian a s Ω A r) (0 : KGSpatialSpace → ℝ)

  receipt_licensed_scalar_reference_dispersion : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A),
    ∀ ξ, kgScalarPrincipalFourierSymbol
      (kgNRFreeComparator (licensedScalarMeaning a s Ω A r).parameters).data ξ =
        ((licensedScalarMeaning a s Ω A r).referenceDispersion ξ : ℂ)

  receipt_licensed_scalar_zero_potential_full_domain : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A),
    (∀ f : KGNRSpatialHilbert,
      f ∈ (kgNRPotentialOperator (0 : KGSpatialSpace → ℝ)).domain) ∧
    kgNRPrincipalCoefficient (licensedScalarMeaning a s Ω A r).parameters =
      -(a.hbar ^ 2 / (2 * a.mass)) ∧
    kgNRPrincipalCoefficient (licensedScalarMeaning a s Ω A r).parameters < 0

  receipt_licensed_scalar_ssq1_comparator : ∀ (A : KGNRObject a) (r : LicensedScalarReceiver a s Ω A)
    {H : LinearPMap ℂ KGNRSpatialHilbert KGNRSpatialHilbert}
    (W : KGScalarSSQ1Witness a H (0 : KGSpatialSpace → ℝ))
    (dispersion : KGFreeInertialDispersion a (kgScalarFreeComparatorOfSSQ1 a W)),
    H = licensedScalarHamiltonian a s Ω A r

  receipt_common_original_preparation_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω (scalarToLicensedMetric a s Ω κ Λ coupling r H))) =
      rayMap _ (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r)

  receipt_common_original_metric_operand_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    restrictedEHMetric a s Ω (licensedEHResponse a s Ω (scalarToLicensedMetric a s Ω κ Λ coupling r H)) =
      originalEHActMetric H.val

  receipt_common_original_metric_source_record_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω})
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)),
    kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (scalarToLicensedMetric a s Ω κ Λ coupling r H))) (kgFamilyQuestionInChart q) =
      licensedScalarOutput a s Ω (scalarBaseObject a) r (kgNROldQuestion q)

  receipt_common_original_registered_reference_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω})
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))),
    (licensedReadout a s Ω (scalarToLicensedMetric a s Ω κ Λ coupling r H) []).answer
      (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q)) =
      (licensedScalarReference a s Ω (scalarBaseObject a) r (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr

  receipt_licensed_scalar_evolved_original_preparation : ∀ (t : ℝ)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a)),
    licensedScalarOriginalPure a s Ω (scalarBaseObject a)
      (licensedScalarContinue a s Ω (scalarBaseObject a) t r) =
      kgNRSpatialOriginalPreparation a t (licensedScalarPure a s Ω (scalarBaseObject a) r)

  receipt_common_evolved_original_preparation_square : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (t : ℝ) (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (scalarToLicensedMetric a s Ω κ Λ coupling
          (licensedScalarContinue a s Ω (scalarBaseObject a) t r) H))) =
      rayMap _ (kgNRSpatialOriginalPreparation a t
        (licensedScalarPure a s Ω (scalarBaseObject a) r))

  receipt_common_preparation_covers_declared_core : ∀ (κ Λ : ℝ) (coupling : κ ≠ 0)
    (x : PureVector (kgOriginalSpatialCore a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}),
    ∃ r : LicensedScalarReceiver a s Ω (scalarBaseObject a),
      licensedScalarPure a s Ω (scalarBaseObject a) r = x ∧
      kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
        (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
          (scalarToLicensedMetric a s Ω κ Λ coupling r H))) =
        rayMap _ (kgPureIsometryMap (kgSpatialCoreOriginalEmbedding a) x)

theorem kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger
    (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    KernelFaithfulLicensedEndpoints a s Ω where
  constraint_first_source := kg_constraint_first_standing_source a s Ω
  current_free_receiving := kg_nr_receiving_qs_constructed a s Ω
  geometric_einstein_receiving κ Λ coupling :=
    (restricted_original_eh_kernel_einstein_receiving a s Ω κ Λ coupling).2
  receipt_current_metric_use_constructs_kernel_and_canonical_license := current_metric_use_constructs_kernel_and_canonical_license a s Ω
  receipt_receiver_has_actual_canonical_license := receiver_has_actual_canonical_license a s Ω
  receipt_present_licensed_history_surjective := present_licensed_history_surjective a s Ω
  receipt_licensed_readout_square := licensed_readout_square a s Ω
  receipt_licensed_response_coverage := licensed_response_coverage a s Ω
  receipt_licensed_source_profile_coverage := licensed_source_profile_coverage a s Ω
  receipt_licensed_response_continuation_square := licensed_response_continuation_square a s Ω
  receipt_licensed_readout_continuation_square := licensed_readout_continuation_square a s Ω
  receipt_licensed_metric_square := licensed_metric_square a s Ω
  receipt_licensed_action_square := licensed_action_square a s Ω
  receipt_licensed_directional_action_square := licensed_directional_action_square a s Ω
  receipt_licensed_original_answer_square := licensed_original_answer_square a s Ω
  receipt_licensed_original_first_failure_square := licensed_original_first_failure_square a s Ω
  receipt_licensed_eh_source_is_original_directional_action := licensed_eh_source_is_original_directional_action a s Ω
  receipt_licensed_eh_same_metric_representation := licensed_eh_same_metric_representation a s Ω
  receipt_licensed_original_failure_square := licensed_original_failure_square a s Ω
  receipt_licensed_rejected_metric_request_stays_failed := licensed_rejected_metric_request_stays_failed a s Ω
  receipt_scalar_use_constructs_kernel_and_canonical_license := scalar_use_constructs_kernel_and_canonical_license a s Ω
  receipt_every_original_scalar_has_canonical_license := every_original_scalar_has_canonical_license a s Ω
  receipt_present_licensed_scalar_surjective := present_licensed_scalar_surjective a s Ω
  receipt_licensed_scalar_meaning_exact := licensed_scalar_meaning_exact a s Ω
  receipt_licensed_scalar_state_coverage := licensed_scalar_state_coverage a s Ω
  receipt_licensed_scalar_old_reference_square := licensed_scalar_old_reference_square a s Ω
  receipt_licensed_scalar_old_complete_record := licensed_scalar_old_complete_record a s Ω
  receipt_licensed_scalar_continuation_reference := licensed_scalar_continuation_reference a s Ω
  receipt_licensed_scalar_continuation_first_failure := licensed_scalar_continuation_first_failure a s Ω
  receipt_licensed_scalar_full_continuation_square := licensed_scalar_full_continuation_square a s Ω
  receipt_licensed_scalar_comparison_reference := licensed_scalar_comparison_reference a s Ω
  receipt_licensed_scalar_region_reference := licensed_scalar_region_reference a s Ω
  receipt_licensed_scalar_tensor_original_square := licensed_scalar_tensor_original_square a s Ω
  receipt_licensed_scalar_domain_graph_receipt := licensed_scalar_domain_graph_receipt a s Ω
  receipt_licensed_scalar_full_flow_receipt := licensed_scalar_full_flow_receipt a s Ω
  receipt_licensed_scalar_exact_generator := licensed_scalar_exact_generator a s Ω
  receipt_licensed_scalar_complete_weak_graph := licensed_scalar_complete_weak_graph a s Ω
  receipt_licensed_scalar_calibrated_comparator := licensed_scalar_calibrated_comparator a s Ω
  receipt_licensed_scalar_free_ssq1 := licensed_scalar_free_ssq1 a s Ω
  receipt_licensed_scalar_reference_dispersion := licensed_scalar_reference_dispersion a s Ω
  receipt_licensed_scalar_zero_potential_full_domain := licensed_scalar_zero_potential_full_domain a s Ω
  receipt_licensed_scalar_ssq1_comparator := licensed_scalar_ssq1_comparator a s Ω
  receipt_common_original_preparation_square := common_original_preparation_square a s Ω
  receipt_common_original_metric_operand_square := common_original_metric_operand_square a s Ω
  receipt_common_original_metric_source_record_square := common_original_metric_source_record_square a s Ω
  receipt_common_original_registered_reference_square := common_original_registered_reference_square a s Ω
  receipt_licensed_scalar_evolved_original_preparation := licensed_scalar_evolved_original_preparation a s Ω
  receipt_common_evolved_original_preparation_square := common_evolved_original_preparation_square a s Ω
  receipt_common_preparation_covers_declared_core := common_preparation_covers_declared_core a s Ω

end AASCKleinGordon.CanonicalLicensing
