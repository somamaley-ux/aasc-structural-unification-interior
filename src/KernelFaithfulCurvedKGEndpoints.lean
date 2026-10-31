import EHKGOriginalAttachedUse
import EHKGOccupiedCauchyData
import EHKGIntegratedActionIdentity
import EHKGFixedMassFlatSpecialization
import KernelFaithfulNativeSREndpoints

/-! Constraint-first Stage 1 composition. The physical specialization is the
constructed nonflat secant-conformal branch of the actual admitted EH operand.
All analytic/use endpoints below are proved, not inputs to the root theorem.
The retained flat SR/free-scalar endpoints are preserved predecessors; a
curved-to-SR or quantitative nonrelativistic limit is not asserted here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open scoped Topology
namespace AASCKleinGordon.CurvedKG

abbrev CurvedCauchyDatum (a : Parameters) :=
  TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)

abbrev CurvedInteriorVariation (a : Parameters) :=
  TestFunction ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩ ℝ (⊤ : ℕ∞)

structure KernelFaithfulCurvedKGEndpoints (a : Parameters) (s : ℝ) : Prop where
  retained_flat_endpoints : CanonicalLicensing.SRIntegration.KernelFaithfulNativeSREndpoints a s (⊤ : Opens CoordinatePoint)
  constraint_first_attachment : ∀ (kappa Lambda : ℝ) (coupling : kappa ≠ 0),
    let D := originalMetricTask a s (⊤ : Opens CoordinatePoint) kappa Lambda
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧ FiveLicensingConclusions D ∧
      constructedLicensing D (curvedOriginalMetricHistory a)
        (originalMetricUseMeaning a s (⊤ : Opens CoordinatePoint) kappa Lambda)
  actual_operand_admitted : conformalOperand (conformalFrequency a) ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint)
  finite_eh_use_admitted : ∀ (kappa Lambda : ℝ), kappa ≠ 0 →
    OriginalEHFiniteUseDomain kappa Lambda wickNativeFlatMetric (conformalOperand (conformalFrequency a))
  domain_open : IsOpen (protectedDiamond (conformalFrequency a))
  domain_occupied : (0 : CoordinatePoint) ∈ protectedDiamond (conformalFrequency a)
  actual_metric_nonflat :
    loweredConnectionCurvature (originalEHActMetric (conformalOperand (conformalFrequency a)))
      (leviCivitaCoefficients (originalEHActMetric (conformalOperand (conformalFrequency a)))) 0 0 1 0 1 ≠ 0
  globally_hyperbolic : EHGloballyHyperbolicOn (conformalFrequency a) (protectedDiamond (conformalFrequency a))
  cauchy_crossing : ∀ curve : InextendibleEHFutureCurve (conformalFrequency a) (protectedDiamond (conformalFrequency a)),
    ∃! p : CoordinatePoint, p ∈ range curve.path ∧ p 0 = 0
  foliation : ∀ p ∈ protectedDiamond (conformalFrequency a),
    ∃ t ∈ evolutionTimeRange (conformalFrequency a), ∃ x ∈ evolutionSliceDomain (conformalFrequency a) t,
      p = evolutionSlicePoint t x
  lapse_normal : ∀ p ∈ protectedDiamond (conformalFrequency a),
    0 < evolutionLapse (conformalFrequency a) p ∧
    wickMatrixQuadratic (originalEHActMetric (conformalOperand (conformalFrequency a)) p)
      (timeUnitNormal (conformalFrequency a) p) = -1 ∧
    ∀ u : CoordinatePoint → ℝ,
      scalarPartial u p 0 = evolutionLapse (conformalFrequency a) p * actualNormalDerivative (conformalFrequency a) u p
  lapse_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (evolutionLapse (conformalFrequency a)) (protectedDiamond (conformalFrequency a))
  shift_zero : ∀ p : CoordinatePoint, evolutionShift (conformalFrequency a) p = 0
  metric_nondegenerate : ∀ p ∈ protectedDiamond (conformalFrequency a),
    (originalEHActMetric (conformalOperand (conformalFrequency a)) p).det ≠ 0
  normal_future : ∀ p ∈ protectedDiamond (conformalFrequency a), 0 < timeUnitNormal (conformalFrequency a) p 0
  normal_orthogonal : ∀ (p v : CoordinatePoint), p ∈ protectedDiamond (conformalFrequency a) → v 0 = 0 →
    coordinateMetricPairing (originalEHActMetric (conformalOperand (conformalFrequency a)) p)
      (timeUnitNormal (conformalFrequency a) p) v = 0
  slices_spacelike : ∀ (p v : CoordinatePoint), p ∈ protectedDiamond (conformalFrequency a) → v 0 = 0 → v ≠ 0 →
    0 < wickMatrixQuadratic (originalEHActMetric (conformalOperand (conformalFrequency a)) p) v
  all_compact_data_cauchy : ∀ f h : CurvedCauchyDatum a,
    let u := compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h
    SameEHKGHistory a u ∧ SameEHCompactCauchyTrace a f h u ∧
      ∀ v : CoordinatePoint → ℝ, SameEHKGHistory a v → SameEHCompactCauchyTrace a f h v →
        EqOn v u (protectedDiamond (conformalFrequency a))
  lf_continuity : Continuous (compactCurvedLocalEvolution a)
  linear_add : ∀ (f h g k : CurvedCauchyDatum a) (p : CoordinatePoint),
    compactCurvedField a (centralLeafDomain (conformalFrequency a)) (f + g) (h + k) p =
      compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h p +
        compactCurvedField a (centralLeafDomain (conformalFrequency a)) g k p
  linear_smul : ∀ (f h : CurvedCauchyDatum a) (r : ℝ) (p : CoordinatePoint),
    compactCurvedField a (centralLeafDomain (conformalFrequency a)) (r • f) (r • h) p =
      r * compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h p
  actual_causal_support : ∀ f h : CurvedCauchyDatum a,
    tsupport (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) ∩
      protectedDiamond (conformalFrequency a) ⊆ metricCausalShadow (conformalFrequency a) (tsupport f ∪ tsupport h)
  nonzero_field_occupied :
    compactCurvedField a (centralLeafDomain (conformalFrequency a)) (occupiedCompactCauchyPosition a) 0 0 = 1
  licensed_metric_exact : ∀ (kappa Lambda : ℝ) (coupling : kappa ≠ 0),
    (licensedReadout a s (⊤ : Opens CoordinatePoint) (curvedLicensedMetricReceiver a s kappa Lambda coupling) []).metric =
      originalEHActMetric (conformalOperand (conformalFrequency a))
  equation_on_actual_licensed_metric : ∀ (kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (f h : CurvedCauchyDatum a) (p : CoordinatePoint), p ∈ protectedDiamond (conformalFrequency a) →
    scalarFieldWaveOperator
      (licensedReadout a s (⊤ : Opens CoordinatePoint) (curvedLicensedMetricReceiver a s kappa Lambda coupling) []).metric
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) p =
        (massWaveNumber a) ^ 2 * compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h p
  same_action_operator : ∀ (u d : CoordinatePoint → ℝ), ContDiff ℝ (⊤ : ℕ∞) u → ContDiff ℝ (⊤ : ℕ∞) d →
    ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldVariationDensity a u d p = actualScalarVariationDivergence a u d p +
        secantScale (conformalFrequency a) (p 0) ^ 4 *
          (scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p -
            (massWaveNumber a) ^ 2 * u p) * d p
  integrable_stationary_action : ∀ (f h : CurvedCauchyDatum a) (d : CurvedInteriorVariation a),
    (∀ t : ℝ, Integrable (fun p : CoordinatePoint =>
      sameEHScalarDensity a (fun q => compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h q + t * d q) p -
        sameEHScalarDensity a (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) p)) ∧
    HasDerivAt (sameEHRelativeFieldAction a (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) d) 0 0
  joint_field_axis : ∀ (u d : CoordinatePoint → ℝ) (H : MetricSourceProbe (⊤ : Opens CoordinatePoint)) (t : ℝ),
    sameEHJointRelativeAction a u d H 0 t = sameEHRelativeFieldAction a u d t
  joint_metric_axis : ∀ (u d : CoordinatePoint → ℝ) (H : MetricSourceProbe (⊤ : Opens CoordinatePoint)) (t : ℝ),
    sameEHJointRelativeAction a u d H t 0 =
      nativeScalarClockRelativeAction (originalEHActMetric (conformalOperand (conformalFrequency a)))
        u ((massWaveNumber a) ^ 2) (t • H)
  action_rescaling_boundary : ∀ (u : CoordinatePoint → ℝ),
    ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a)) →
    ∀ (K : Compacts CoordinatePoint), (K : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a) →
    (∫ p in (K : Set CoordinatePoint), sameEHScalarDensity a u p) =
      (∫ p in (K : Set CoordinatePoint), nativeRealClockDensity metric
        (scalarPartial (secantLift (conformalFrequency a) u) p)
        (secantLift (conformalFrequency a) u p) (conformalFrequency a ^ 2)) -
      (1 / 2 : ℝ) * ∫ p in (K : Set CoordinatePoint),
        scalarPartial (secantBoundaryFlux (conformalFrequency a) u) p 0
  initial_observations : ∀ (f h : CurvedCauchyDatum a) (x : KGSpatialSpace), x ∈ centralLeafDomain (conformalFrequency a) →
    scalarQuestionAnswer a (initialCurvedScalarUseState a f h) (.value (centralLeafPoint x)) = some (f x) ∧
    scalarQuestionAnswer a (initialCurvedScalarUseState a f h) (.normal (centralLeafPoint x)) = some (h x)
  data_faithful : ∀ f h g k : CurvedCauchyDatum a,
    (∀ q, scalarQuestionAnswer a (initialCurvedScalarUseState a f h) q =
      scalarQuestionAnswer a (initialCurvedScalarUseState a g k) q) → f = g ∧ h = k
  finite_programs : ∀ (program : List CurvedKGOperation) (state other : CurvedScalarUseState a),
    ScalarUseSame a state other →
    ScalarUseSame a (curvedKGRun a state program).1 (curvedKGRun a other program).1 ∧
      (curvedKGRun a state program).2 = (curvedKGRun a other program).2
  first_failures : ∀ (program : List CurvedKGOperation) (state other : CurvedScalarUseState a),
    ScalarUseSame a state other →
    firstCurvedKGFailure (curvedKGRun a state program).2 = firstCurvedKGFailure (curvedKGRun a other program).2
  original_attached_records : ∀ (kappa Lambda : ℝ) (coupling : kappa ≠ 0) (state : CurvedScalarUseState a)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint))) (program : List CurvedKGOperation),
    licensedCurvedUseRecord a s kappa Lambda coupling state ops program = rawCurvedUseRecord a s kappa Lambda state ops program
  original_empty_word_actual_program : ∀ (kappa Lambda : ℝ) (coupling : kappa ≠ 0) (state : CurvedScalarUseState a)
    (program : List CurvedKGOperation),
    (licensedCurvedUseRecord a s kappa Lambda coupling state [] program).2 = (curvedKGRun a state program).2
  metric_change_rejection : ∀ (metric : CoordinatePoint → Tensor2) (state : CurvedScalarUseState a) (program : List CurvedKGOperation),
    metric ≠ originalEHActMetric (conformalOperand (conformalFrequency a)) →
      scalarEventsAtOriginalMetric a metric state program = [⟨none, some (.inl .incompatibleMetric)⟩]
  continuation_agrees : ∀ (state : CurvedScalarUseState a) (request : ScalarContinuationRequest)
    (nonzero : request.scale ≠ 0) (inside : scalarContinuationDomain a request ≤ state.domain),
    scalarContinuationDataMatch a state request →
      EqOn (continuedCurvedScalarState a state request inside).field state.field (scalarContinuationDomain a request)
  continuation_all_compact_data : ∀ f h : CurvedCauchyDatum a,
    ∃ time : ℝ, time ≠ 0 ∧ ∃ scale : ℝ, 0 < scale ∧ ∃ result : CurvedScalarUseState a,
      scalarContinue a (initialCurvedScalarUseState a f h) (evaluatedScalarContinuation a f h time scale) = .ok result ∧
      result.domain = scalarContinuationDomain a (evaluatedScalarContinuation a f h time scale) ∧
      EqOn result.field (initialCurvedScalarUseState a f h).field result.domain
  continuation_identity : ∀ f h : CurvedCauchyDatum a, ∃ result : CurvedScalarUseState a,
    scalarContinue a (initialCurvedScalarUseState a f h) (evaluatedScalarContinuation a f h 0 1) = .ok result ∧
      ScalarUseSame a result (initialCurvedScalarUseState a f h)
  continuation_composition : ∀ (state : CurvedScalarUseState a)
    (first : ScalarContinuationRequest) (nonzeroFirst : first.scale ≠ 0)
    (insideFirst : scalarContinuationDomain a first ≤ state.domain)
    (matchingFirst : scalarContinuationDataMatch a state first)
    (second : ScalarContinuationRequest) (nonzeroSecond : second.scale ≠ 0)
    (insideSecond : scalarContinuationDomain a second ≤ scalarContinuationDomain a first)
    (matchingSecond : scalarContinuationDataMatch a (continuedCurvedScalarState a state first insideFirst) second),
    ScalarUseSame a
      (continuedCurvedScalarState a (continuedCurvedScalarState a state first insideFirst) second insideSecond)
      (restrictCurvedScalarUseState a state (scalarContinuationDomain a second) (insideSecond.trans insideFirst))
  continuation_all_programs : ∀ (state : CurvedScalarUseState a) (request : ScalarContinuationRequest)
    (nonzero : request.scale ≠ 0) (inside : scalarContinuationDomain a request ≤ state.domain),
    scalarContinuationDataMatch a state request → ∀ program : List CurvedKGOperation,
    (curvedKGRun a (continuedCurvedScalarState a state request inside) program).2 =
        (curvedKGRun a (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) program).2 ∧
    firstCurvedKGFailure (curvedKGRun a (continuedCurvedScalarState a state request inside) program).2 =
        firstCurvedKGFailure (curvedKGRun a (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) program).2
  fixed_mass_flat_operator : ∀ (mu2 : ℝ) (u : CoordinatePoint → ℝ) (p : CoordinatePoint),
    scalarFieldWaveOperator (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint))) u p - mu2 * u p =
      -flatScalarResidual mu2 u p
  fixed_mass_flat_equation : ∀ (U : Opens KGSpatialSpace) (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint),
    scalarFieldWaveOperator (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)))
      (compactFlatField a U f h) p = (massWaveNumber a) ^ 2 * compactFlatField a U f h p
  fixed_mass_flat_fourier : ∀ (U : Opens KGSpatialSpace) (f h : TestFunction U ℝ (⊤ : ℕ∞)) (p : CoordinatePoint),
    compactFlatField a U f h p = Complex.reCLM (fullFlatPosition a
      (compactCauchySchwartzCLM U f) (compactCauchySchwartzCLM U h) (p 0) (coordinateSpatialCLM p))
  fixed_mass_flat_traces : ∀ (U : Opens KGSpatialSpace) (f h : TestFunction U ℝ (⊤ : ℕ∞)) (x : KGSpatialSpace),
    compactFlatField a U f h (centralLeafPoint x) = f x ∧
      scalarPartial (compactFlatField a U f h) (centralLeafPoint x) 0 = h x

theorem kernel_faithful_same_eh_curved_kg (a : Parameters) (s : ℝ) : KernelFaithfulCurvedKGEndpoints a s where
  retained_flat_endpoints := CanonicalLicensing.SRIntegration.kernel_faithful_native_sr_canonical_licensing_eh_scalar a s _
  constraint_first_attachment := curved_original_task_kernel_licensing a s
  actual_operand_admitted := conformal_operand_admitted _
  finite_eh_use_admitted := curved_original_finite_eh_use_admitted a
  domain_open := protected_diamond_open _
  domain_occupied := protected_diamond_zero _
  actual_metric_nonflat := (protected_same_eh_nonflat a).2.2
  globally_hyperbolic := protected_diamond_globally_hyperbolic _
  cauchy_crossing := central_leaf_cauchy_crossing _
  foliation := diamond_foliated_by_slices _
  lapse_normal p hp := ⟨evolution_lapse_positive _ p hp, time_unit_normal_unit _ p hp,
    fun u => coordinate_time_normal_derivative _ u p hp⟩
  lapse_smooth := evolution_lapse_smooth _
  shift_zero _ := rfl
  metric_nondegenerate p hp := by
    rw [protected_metric_identity _ p (protected_diamond_subset_ball _ hp), time_conformal_determinant]
    exact neg_ne_zero.mpr (pow_ne_zero 8 (inv_ne_zero (ne_of_gt
      (protected_cosine_positive _ p (protected_diamond_subset_ball _ hp)))))
  normal_future := time_unit_normal_future _
  normal_orthogonal := time_unit_normal_orthogonal _
  slices_spacelike := constant_time_slice_spacelike _
  all_compact_data_cauchy := all_compact_same_eh_cauchy_exists_unique a
  lf_continuity := compact_curved_local_evolution_lf_continuous a
  linear_add := compact_curved_field_add a _
  linear_smul := compact_curved_field_smul a _
  actual_causal_support := compact_curved_closed_support_in_metric_causal_shadow a
  nonzero_field_occupied := occupied_curved_cauchy_field_nonzero a
  licensed_metric_exact := curved_licensed_metric_exact a s
  equation_on_actual_licensed_metric := compact_curved_equation_on_actual_licensed_metric a s
  same_action_operator := same_eh_scalar_euler_lagrange_identity a
  integrable_stationary_action := compact_curved_same_action_variation_endpoint a
  joint_field_axis u d H t := same_eh_joint_action_field_axis a u d H t
  joint_metric_axis u d H t := same_eh_joint_action_metric_axis a u d H t
  action_rescaling_boundary := integrated_same_eh_action_density_boundary a
  initial_observations f h x hx := ⟨initial_scalar_position_answer a f h x hx, initial_scalar_normal_answer a f h x hx⟩
  data_faithful := compact_cauchy_observations_faithful a
  finite_programs := curved_kg_run_same a
  first_failures := curved_kg_first_failure_same a
  original_attached_records := licensed_curved_original_record_square a s
  original_empty_word_actual_program := licensed_curved_empty_original_all_uses a s
  metric_change_rejection := original_incompatible_metric_stays_failed a
  continuation_agrees := continued_state_agrees a
  continuation_all_compact_data := all_compact_data_genuine_slice_continuation a
  continuation_identity := evaluated_continuation_identity a
  continuation_composition := continued_state_composition a
  continuation_all_programs := continuation_retains_all_curved_programs a
  fixed_mass_flat_operator := zero_eh_operator_is_original_flat
  fixed_mass_flat_equation := fixed_mass_flat_same_eh_equation a
  fixed_mass_flat_fourier := fixed_mass_flat_field_is_inherited_fourier a
  fixed_mass_flat_traces U f h x := ⟨fixed_mass_flat_initial_position a U f h x,
    fixed_mass_flat_initial_velocity a U f h x⟩

end AASCKleinGordon.CurvedKG
