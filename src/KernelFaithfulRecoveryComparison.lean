import RCDispersionError
import RCMomentumCutoff
import RCQuantitativeMomentum
import RCUniformMomentum
import RCFourierRecovery
import RCObservationBounds
import RCOriginalComparisonReadout
import RCSameDataFields
import RCInitialSourceComparison
import RCRealEvaluationReaders
import RCDilationDomain
import RCMetricObservationBounds
import RCDurationComparison
import RCGuardedGeometricDuration
import KernelFaithfulSameActionKGSource
import KGS36FreeComparatorAssembly

/-! Constraint-first recovery composition on the declared constructed sectors.
Every receipt is a proved statement on actual source/preparation/evolution maps.
No conclusion certificate is an argument of the root. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion AASCMetricConstruction
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource AASCKleinGordon.CanonicalLicensing
open scoped Topology Interval
namespace AASCKleinGordon.RecoveryComparison
open KGQuantum W9
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

structure KernelFaithfulRecoveryComparison (a : Parameters) (s kappa Lambda : ℝ) : Prop where
  retained_stage2 : SameActionKGSourceEndpoints a s kappa Lambda
  retained_original_license : ∀ Ω : Opens CoordinatePoint, KernelFaithfulLicensedEndpoints a s Ω
  receipt_dispersion_error_exact : ∀ (c : ℝ) (hc : 0 < c) (p : Momentum),
    kgNRKineticEnergy a p - kgNRDispersion a c p =
      momentumSq p ^ 2 /
        (2*a.mass*c^2*(Real.sqrt (a.mass^2+momentumSq p/c^2)+a.mass)^2)
  receipt_original_energy_error : ∀ (c : ℝ) (hc : 0 < c) (p : Momentum),
    0 ≤ kgNRKineticEnergy a p - (energy (kgNRParameters a c hc) p - a.mass*c^2) ∧
    kgNRKineticEnergy a p - (energy (kgNRParameters a c hc) p - a.mass*c^2) ≤
      momentumSq p^2/(8*a.mass^3*c^2)
  receipt_momentum_cutoff_ae : ∀ (P : ℝ) (f : KGNRMomentumHilbert),
    momentumCutoff P f =ᵐ[volume] (fun p => cutoffSymbol P p * f p)
  receipt_momentum_cutoff_contraction : ∀ (P : ℝ) (f : KGNRMomentumHilbert),
    ‖momentumCutoff P f‖ ≤ ‖f‖
  receipt_momentum_cutoff_idempotent : ∀ (P : ℝ) (f : KGNRMomentumHilbert),
    momentumCutoff P (momentumCutoff P f) = momentumCutoff P f
  receipt_momentum_cutoff_strong_exhaustion : ∀ (f : KGNRMomentumHilbert),
    Tendsto (fun P : ℝ => momentumCutoff P f) atTop (𝓝 f)
  receipt_momentum_cutoff_evolution_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert),
    ‖kgNRMomentumFlow a c t (momentumCutoff P f)-kgNRFreeMomentumFlow a t (momentumCutoff P f)‖ ≤
      min 2 (cutoffError a c t P)*‖f‖
  receipt_cutoff_evolution_operator_bound : ∀ (c : ℝ) (hc : 0 < c) (t P : ℝ),
    ‖cutoffEvolutionDifference a c t P‖ ≤ min 2 (cutoffError a c t P)
  receipt_momentum_evolution_tail_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert),
    ‖kgNRMomentumFlow a c t f-kgNRFreeMomentumFlow a t f‖ ≤
      cutoffError a c t P*‖f‖+2*‖f-momentumCutoff P f‖
  receipt_momentum_compact_time_strong : ∀ (f : KGNRMomentumHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgNRMomentumFlow a c t f-kgNRFreeMomentumFlow a t f‖ < epsilon
  receipt_original_covariant_compact_time_strong : ∀ (f : KGNRMomentumHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgTransportedOriginalRestFlow a c t f-kgNRFreeMomentumFlow a t f‖ < epsilon
  receipt_original_isolated_compact_time_strong : ∀ (f : KGNRMomentumHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgTransportedIsolatedRestFlow a c t f-kgNRFreeMomentumFlow a t f‖ < epsilon
  receipt_original_covariant_cutoff_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert),
    ‖kgTransportedOriginalRestFlow a c t (momentumCutoff P f)-
      kgNRFreeMomentumFlow a t (momentumCutoff P f)‖ ≤ min 2 (cutoffError a c t P)*‖f‖
  receipt_original_isolated_cutoff_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert),
    ‖kgTransportedIsolatedRestFlow a c t (momentumCutoff P f)-
      kgNRFreeMomentumFlow a t (momentumCutoff P f)‖ ≤ min 2 (cutoffError a c t P)*‖f‖
  receipt_actual_covariant_preparation_evolution_square : ∀ (c : ℝ) (hc : 0 < c)
    (t : ℝ) (f : KGNRMomentumHilbert),
    kgCovariantMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualCovariantRestFlow a c hc t (covariantRecoveryPreparation a c hc f)) =
      kgNRMomentumFlow a c t f
  receipt_actual_isolated_preparation_evolution_square : ∀ (c : ℝ) (hc : 0 < c)
    (t : ℝ) (f : KGNRMomentumHilbert),
    kgIsolatedMomentumUnitary (kgNRParameters a c hc)
      (kgNRActualIsolatedRestFlow a c hc t (isolatedRecoveryPreparation a c hc f)) =
      kgNRMomentumFlow a c t f
  receipt_spatial_cutoff_evolution_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRSpatialHilbert),
    ‖kgOriginalRestSpatialFlow a c t (spatialCutoff a P f)-
      kgNRSpatialFreeFlow a t (spatialCutoff a P f)‖ ≤ min 2 (cutoffError a c t P)*‖f‖
  receipt_spatial_compact_time_strong : ∀ (f : KGNRSpatialHilbert)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgOriginalRestSpatialFlow a c t f-kgNRSpatialFreeFlow a t f‖ < epsilon
  receipt_original_core_compact_time_strong : ∀ (x : kgOriginalSpatialCore a)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖kgOriginalRestSpatialFlow a c t x.val-(kgNRSpatialCoreFlow a t x).val‖ < epsilon
  receipt_momentum_linear_observation_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f : KGNRMomentumHilbert) (L : KGNRMomentumHilbert →L[ℂ] ℂ),
    ‖L (kgNRMomentumFlow a c t f)-L (kgNRFreeMomentumFlow a t f)‖ ≤
      ‖L‖*(cutoffError a c t P*‖f‖+2*‖f-momentumCutoff P f‖)
  receipt_momentum_probability_bound : ∀ (c : ℝ) (hc : 0 < c)
    (t P : ℝ) (f z : KGNRMomentumHilbert) (hf : ‖f‖=1) (hz : ‖z‖=1),
    |‖inner ℂ z (kgNRMomentumFlow a c t f)‖^2-‖inner ℂ z (kgNRFreeMomentumFlow a t f)‖^2| ≤
      2*(cutoffError a c t P*‖f‖+2*‖f-momentumCutoff P f‖)
  receipt_spatial_linear_observation_compact_time : ∀ (f : KGNRSpatialHilbert)
    (L : KGNRSpatialHilbert →L[ℂ] ℂ) (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖L (kgOriginalRestSpatialFlow a c t f)-L (kgNRSpatialFreeFlow a t f)‖ < epsilon
  receipt_spatial_probability_compact_time : ∀ (f z : KGNRSpatialHilbert)
    (hf : ‖f‖=1) (hz : ‖z‖=1) (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      |‖inner ℂ z (kgOriginalRestSpatialFlow a c t f)‖^2-
        ‖inner ℂ z (kgNRSpatialFreeFlow a t f)‖^2| < epsilon
  receipt_original_core_comparison_readout : ∀ (s t : ℝ) (Ω : Opens CoordinatePoint)
    (x z : PureVector (kgOriginalSpatialCore a)),
    kgSpatialSourceRecord a s Ω (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x))
      (.reverseComparison (kgPureIsometryMap (K := fockCoreDomain a) (kgSpatialCoreOriginalEmbedding a) z)) =
        .comparison (originalCoreComparisonValue a t x z)
  receipt_original_core_comparison_is_normalized_overlap : ∀ (t : ℝ)
    (x z : PureVector (kgOriginalSpatialCore a)) (hx : ‖x.val‖=1) (hz : ‖z.val‖=1),
    originalCoreComparisonValue a t x z = ‖inner ℂ z.val.val (kgNRSpatialFreeFlow a t x.val.val)‖^2
  receipt_original_numeric_comparison_compact_time : ∀ (x z : PureVector (kgOriginalSpatialCore a)) (hx : ‖x.val‖=1) (hz : ‖z.val‖=1)
    (T : ℝ) (hT : 0 ≤ T) (epsilon : ℝ) (positive : 0 < epsilon),
    ∀ᶠ c : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      |‖inner ℂ z.val.val (kgOriginalRestSpatialFlow a c t x.val.val)‖^2-
        originalCoreComparisonValue a t x z| < epsilon
  receipt_same_data_initial_values : ∀ (f h : CurvedCauchyDatum a) (x : KGSpatialSpace),
    sourceField a f h (spaceTimePoint 0 x) = flatComparisonField a f h (spaceTimePoint 0 x)
  receipt_same_data_initial_time_jets : ∀ (f h : CurvedCauchyDatum a) (x : KGSpatialSpace),
    scalarPartial (sourceField a f h) (spaceTimePoint 0 x) 0 =
      scalarPartial (flatComparisonField a f h) (spaceTimePoint 0 x) 0
  receipt_compact_leaf_has_common_slab : ∀ (K : Set KGSpatialSpace)
    (compact : IsCompact K) (interior : K ⊆ centralLeafDomain (conformalFrequency a)),
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K, spaceTimePoint t x ∈ sourceDomain a
  receipt_same_data_local_evolved_comparison : ∀ (f h : CurvedCauchyDatum a)
    (K : Set KGSpatialSpace) (compact : IsCompact K)
    (interior : K ⊆ centralLeafDomain (conformalFrequency a)),
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      (∀ t : ℝ, |t| ≤ r → ∀ x ∈ K, spaceTimePoint t x ∈ sourceDomain a) ∧
      ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K,
        |sourceField a f h (spaceTimePoint t x)-flatComparisonField a f h (spaceTimePoint t x)| ≤ C*t^2 ∧
        |scalarPartial (sourceField a f h) (spaceTimePoint t x) 0-
          scalarPartial (flatComparisonField a f h) (spaceTimePoint t x) 0| ≤ C*|t|
  receipt_same_data_initial_all_jets : ∀ (f h : CurvedCauchyDatum a) (x : KGSpatialSpace),
    scalarPartial (sourceField a f h) (centralLeafPoint x) =
      scalarPartial (flatComparisonField a f h) (centralLeafPoint x)
  receipt_same_initial_metric : ∀ (x : KGSpatialSpace)
    (inside : x ∈ centralLeafDomain (conformalFrequency a)),
    sourceMetric a (centralLeafPoint x) =
      originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) (centralLeafPoint x)
  receipt_same_data_initial_density : ∀ (f h : CurvedCauchyDatum a)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)),
    sameEHScalarDensity a (sourceField a f h) (centralLeafPoint x) =
      nativeRealClockDensity
        (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)) (centralLeafPoint x))
        (scalarPartial (flatComparisonField a f h) (centralLeafPoint x))
        (flatComparisonField a f h (centralLeafPoint x)) (massWaveNumber a^2)
  receipt_same_data_initial_canonical_momentum : ∀ (f h : CurvedCauchyDatum a)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)),
    actualScalarCanonicalMomentum a (sourceField a f h) (centralLeafPoint x) =
      scalarCanonicalMomentum 1 (scalarPartial (flatComparisonField a f h) (centralLeafPoint x) 0)
  receipt_same_data_initial_stress : ∀ (f h : CurvedCauchyDatum a)
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)),
    sameSourceStress a (sourceField a f h) (centralLeafPoint x) =
      scalarFieldStress (originalEHActMetric (0 : MetricSourceProbe (⊤ : Opens CoordinatePoint)))
        (flatComparisonField a f h) (massWaveNumber a^2) (centralLeafPoint x)
  receipt_evaluation_domain_exact : ∀ (f h : CurvedCauchyDatum a)
    (curved : Bool) (q : EvaluationQuestion),
    (evaluationRead a f h curved q).isSome = true ↔ q.2 ∈ sourceDomain a
  receipt_evaluation_first_domain_failure_exact : ∀ (f h : CurvedCauchyDatum a)
    (questions : List EvaluationQuestion),
    evaluationFirstFailure a f h true questions = evaluationFirstFailure a f h false questions
  receipt_curved_value_reader_is_original : ∀ (f h : CurvedCauchyDatum a) (p : CoordinatePoint),
    evaluationRead a f h true (.value,p) =
      scalarQuestionAnswer a (initialCurvedScalarUseState a f h) (.value p)
  receipt_actual_evaluation_comparison : ∀ (f h : CurvedCauchyDatum a)
    (K : Set KGSpatialSpace) (compact : IsCompact K)
    (interior : K ⊆ centralLeafDomain (conformalFrequency a)),
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K,
      (∃ u v : ℝ, evaluationRead a f h true (.value,spaceTimePoint t x)=some u ∧
        evaluationRead a f h false (.value,spaceTimePoint t x)=some v ∧ |u-v| ≤ C*t^2) ∧
      (∃ u v : ℝ, evaluationRead a f h true (.coordinateTimeJet,spaceTimePoint t x)=some u ∧
        evaluationRead a f h false (.coordinateTimeJet,spaceTimePoint t x)=some v ∧ |u-v| ≤ C*|t|)
  receipt_same_data_physical_time_comparison : ∀ (f h : CurvedCauchyDatum a)
    (K : Set KGSpatialSpace) (compact : IsCompact K)
    (interior : K ⊆ centralLeafDomain (conformalFrequency a)),
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ r → ∀ x ∈ K,
      spaceTimePoint (a.speed*t) x ∈ sourceDomain a ∧
      |sourceField a f h (spaceTimePoint (a.speed*t) x)-flatComparisonField a f h (spaceTimePoint (a.speed*t) x)| ≤ C*t^2 ∧
      |deriv (fun s => sourceField a f h (spaceTimePoint (a.speed*s) x)) t-
        deriv (fun s => flatComparisonField a f h (spaceTimePoint (a.speed*s) x)) t| ≤ C*|t|
  receipt_actual_dilation_derivative : ∀ (epsilon : ℝ) (y : CoordinatePoint),
    HasFDerivAt (fun p : CoordinatePoint => epsilon • p) (dilationCLM epsilon) y
  receipt_actual_dilation_pullback_formula : ∀ (epsilon : ℝ) (y : CoordinatePoint),
    actualDilationPullback a epsilon y = epsilon^2 • normalizedRescaledMetric a epsilon y
  receipt_compact_dilation_receiving_domain : ∀ (K : Set CoordinatePoint) (compact : IsCompact K),
    ∃ epsilon0 B : ℝ, 0 < epsilon0 ∧ 0 < B ∧
      (∀ y ∈ K, diamondGauge y ≤ B) ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ epsilon0 → ∀ y ∈ K,
        epsilon • y ∈ sourceDomain a ∧ |conformalFrequency a*(epsilon • y) 0| ≤ (1:ℝ)/2
  receipt_normalized_metric_quadratic_error : ∀ (epsilon : ℝ) (y v : CoordinatePoint)
    (inside : epsilon • y ∈ sourceDomain a)
    (small : |conformalFrequency a*(epsilon • y) 0| ≤ (1:ℝ)/2),
    |wickMatrixQuadratic (normalizedRescaledMetric a epsilon y) v-wickMatrixQuadratic metric v| ≤
      6*(conformalFrequency a*(epsilon • y) 0)^2*|wickMatrixQuadratic metric v|
  receipt_source_origin_matches_constructed_sr_form : ∀ (z : AASCKleinGordon.CanonicalLicensing.SRIntegration.SREvent),
    comparisonQuadratic (sourceMetric a 0)
      (AASCKleinGordon.CanonicalLicensing.SRIntegration.srEventCoordinates z) =
      -AASCKleinGordon.CanonicalLicensing.SRIntegration.srOriginalOrderQuadratic z
  receipt_scaled_duration_integrand_error : ∀ (epsilon B : ℝ) (p v : CoordinatePoint)
    (_he : 0 ≤ epsilon) (hB : 0 ≤ B) (pointBound : |p 0| ≤ B)
    (inside : epsilon • p ∈ sourceDomain a) (small : |conformalFrequency a*(epsilon • p) 0| ≤ (1:ℝ)/2),
    |durationRate a (normalizedRescaledMetric a epsilon p) v-durationRate a metric v| ≤
      (2*conformalFrequency a^2*B^2)*epsilon^2*durationRate a metric v
  receipt_fixed_metric_scaled_path_comparison : ∀ (y : ℝ → CoordinatePoint)
    (regular : ContDiff ℝ 1 y) (b e : ℝ) (order : b ≤ e),
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ 0 ≤ C ∧
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ epsilon0 →
        (∀ s ∈ Icc b e, epsilon • y s ∈ sourceDomain a) ∧
        |(∫ s in b..e, durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s))-
          (∫ s in b..e, durationRate a metric (deriv y s))| ≤ C*epsilon^2 ∧
        (∫ s in b..e, durationRate a (sourceMetric a (epsilon • y s)) (deriv (fun t => epsilon • y t) s)) =
          epsilon*(∫ s in b..e, durationRate a (normalizedRescaledMetric a epsilon (y s)) (deriv y s))
  receipt_scaled_future_timelike : ∀ (y : ℝ → CoordinatePoint)
    (regular : ContDiff ℝ 1 y) (b e delta epsilon : ℝ) (margin : futureTimelikeMargin y b e delta)
    (he : 0 < epsilon) (_domain : ∀ s ∈ Icc b e, epsilon • y s ∈ sourceDomain a)
    (s : ℝ) (hs : s ∈ Icc b e),
    0 < deriv (fun t => epsilon • y t) s 0 ∧
      wickMatrixQuadratic (sourceMetric a (epsilon • y s)) (deriv (fun t => epsilon • y t) s) < 0
  receipt_guarded_scaled_geometric_duration : ∀ (y : ℝ → CoordinatePoint)
    (regular : ContDiff ℝ 1 y) (b e delta : ℝ) (order : b ≤ e)
    (margin : futureTimelikeMargin y b e delta),
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ 0 ≤ C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon0 →
      geometricDurationApplicable a (fun t => epsilon • y t) b e ∧
      ∃ value : ℝ, geometricDurationRead a (fun t => epsilon • y t) b e = some value ∧
        |value-epsilon*(∫ s in b..e, durationRate a metric (deriv y s))| ≤ C*epsilon^3
  receipt_kg_nr_spatial_evolved_complete_original_record : ∀ (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)),
    kgSpatialSourceRecord a s Ω
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x)) q =
      kgFamilyOutput a s Ω (kgOriginalObject a) (kgNRSpatialOriginalPreparation a t x) q
  receipt_kg_nr_spatial_evolved_original_reference : ∀ (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))),
    kgSpatialSourceReference a s Ω
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x)) q =
      (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).references.referenceAt
        (kgNRSpatialOriginalPreparation a t x) q
  receipt_kg_nr_spatial_evolved_original_first_failure : ∀ (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a))
    (word : List (KGFamilyQuestion a Ω (kgOriginalObject a))),
    kgFirstFailure (kgSpatialSourceRecord a s Ω
      (rayMap _ (PureVector.mapUnitary (kgNRSpatialCoreFlow a t) x))) word =
      kgFirstFailure (kgFamilyOutput a s Ω (kgOriginalObject a)
        (kgNRSpatialOriginalPreparation a t x)) word
  receipt_kg_nr_spatial_evolved_original_source_attachment : ∀ (s t : ℝ)
    (Ω : Opens CoordinatePoint) (x : PureVector (kgOriginalSpatialCore a)),
    kgW9OriginalResponse a s Ω
      (rayMap _ (kgNRSpatialOriginalPreparation a t x)) =
      (wickMetricPathF a s Ω (wickMetricPathPiA a s Ω
        (wickCommonRoleSourcePresentation a s Ω
          (kgOriginalQuantumToRay a (rayMap _ (kgNRSpatialOriginalPreparation a t x)))))).val
  receipt_kg_nr_spatial_exact_generator : GlobalCharge.ExactGenerator (Translation.coefficient a.hbar)
      (kgNRSpatialFreeFlow a) (kgNRSpatialKinetic a)
  receipt_kg_nr_spatial_kinetic_weak_graph : ∀ (f g : KGNRSpatialHilbert),
    (f,g) ∈ (kgNRSpatialKinetic a).graph ↔ kgSpatialWeakKineticGraph a f g
  receipt_kg_source_free_s36_comparator_endpoint : ∀ (s : ℝ) (Ω : Opens CoordinatePoint),
    KGNRReceivingQS a s Ω ∧
    KGFreeInertialDispersion a (kgNRFreeComparator a) ∧
    (∀ (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert)
      (C : KGScalarFreeComparator H),
      KGFreeAnchoredDispersionAt a C → H = kgNRSpatialKinetic a) ∧
    (∀ (H : KGNRSpatialHilbert →ₗ.[ℂ] KGNRSpatialHilbert)
      (W : KGScalarSSQ1Witness a H (0 : KGSpatialSpace → ℝ)),
      KGFreeInertialDispersion a (kgScalarFreeComparatorOfSSQ1 a W) →
        H = kgNRSpatialKinetic a)

theorem kernel_faithful_recovery_comparison (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    KernelFaithfulRecoveryComparison a s kappa Lambda where
  retained_stage2 := kernel_faithful_same_action_kg_source a s kappa Lambda coupling
  retained_original_license := kernel_faithful_canonical_licensing_to_eh_and_free_schrodinger a s
  receipt_dispersion_error_exact := dispersion_error_exact a
  receipt_original_energy_error := original_energy_error a
  receipt_momentum_cutoff_ae := momentum_cutoff_ae
  receipt_momentum_cutoff_contraction := momentum_cutoff_contraction
  receipt_momentum_cutoff_idempotent := momentum_cutoff_idempotent
  receipt_momentum_cutoff_strong_exhaustion := momentum_cutoff_strong_exhaustion
  receipt_momentum_cutoff_evolution_bound := momentum_cutoff_evolution_bound a
  receipt_cutoff_evolution_operator_bound := cutoff_evolution_operator_bound a
  receipt_momentum_evolution_tail_bound := momentum_evolution_tail_bound a
  receipt_momentum_compact_time_strong := momentum_compact_time_strong a
  receipt_original_covariant_compact_time_strong := original_covariant_compact_time_strong a
  receipt_original_isolated_compact_time_strong := original_isolated_compact_time_strong a
  receipt_original_covariant_cutoff_bound := original_covariant_cutoff_bound a
  receipt_original_isolated_cutoff_bound := original_isolated_cutoff_bound a
  receipt_actual_covariant_preparation_evolution_square := actual_covariant_preparation_evolution_square a
  receipt_actual_isolated_preparation_evolution_square := actual_isolated_preparation_evolution_square a
  receipt_spatial_cutoff_evolution_bound := spatial_cutoff_evolution_bound a
  receipt_spatial_compact_time_strong := spatial_compact_time_strong a
  receipt_original_core_compact_time_strong := original_core_compact_time_strong a
  receipt_momentum_linear_observation_bound := momentum_linear_observation_bound a
  receipt_momentum_probability_bound := momentum_probability_bound a
  receipt_spatial_linear_observation_compact_time := spatial_linear_observation_compact_time a
  receipt_spatial_probability_compact_time := spatial_probability_compact_time a
  receipt_original_core_comparison_readout := original_core_comparison_readout a
  receipt_original_core_comparison_is_normalized_overlap := original_core_comparison_is_normalized_overlap a
  receipt_original_numeric_comparison_compact_time := original_numeric_comparison_compact_time a
  receipt_same_data_initial_values := same_data_initial_values a
  receipt_same_data_initial_time_jets := same_data_initial_time_jets a
  receipt_compact_leaf_has_common_slab := compact_leaf_has_common_slab a
  receipt_same_data_local_evolved_comparison := same_data_local_evolved_comparison a
  receipt_same_data_initial_all_jets := same_data_initial_all_jets a
  receipt_same_initial_metric := same_initial_metric a
  receipt_same_data_initial_density := same_data_initial_density a
  receipt_same_data_initial_canonical_momentum := same_data_initial_canonical_momentum a
  receipt_same_data_initial_stress := same_data_initial_stress a
  receipt_evaluation_domain_exact := evaluation_domain_exact a
  receipt_evaluation_first_domain_failure_exact := evaluation_first_domain_failure_exact a
  receipt_curved_value_reader_is_original := curved_value_reader_is_original a
  receipt_actual_evaluation_comparison := actual_evaluation_comparison a
  receipt_same_data_physical_time_comparison := same_data_physical_time_comparison a
  receipt_actual_dilation_derivative := actual_dilation_derivative
  receipt_actual_dilation_pullback_formula := actual_dilation_pullback_formula a
  receipt_compact_dilation_receiving_domain := compact_dilation_receiving_domain a
  receipt_normalized_metric_quadratic_error := normalized_metric_quadratic_error a
  receipt_source_origin_matches_constructed_sr_form := source_origin_matches_constructed_sr_form a
  receipt_scaled_duration_integrand_error := scaled_duration_integrand_error a
  receipt_fixed_metric_scaled_path_comparison := fixed_metric_scaled_path_comparison a
  receipt_scaled_future_timelike := scaled_future_timelike a
  receipt_guarded_scaled_geometric_duration := guarded_scaled_geometric_duration a
  receipt_kg_nr_spatial_evolved_complete_original_record := kg_nr_spatial_evolved_complete_original_record a
  receipt_kg_nr_spatial_evolved_original_reference := kg_nr_spatial_evolved_original_reference a
  receipt_kg_nr_spatial_evolved_original_first_failure := kg_nr_spatial_evolved_original_first_failure a
  receipt_kg_nr_spatial_evolved_original_source_attachment := kg_nr_spatial_evolved_original_source_attachment a
  receipt_kg_nr_spatial_exact_generator := kg_nr_spatial_exact_generator a
  receipt_kg_nr_spatial_kinetic_weak_graph := kg_nr_spatial_kinetic_weak_graph a
  receipt_kg_source_free_s36_comparator_endpoint := kg_source_free_s36_comparator_endpoint a

end AASCKleinGordon.RecoveryComparison
