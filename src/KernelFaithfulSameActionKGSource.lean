import SKGMetricRayCompletion
import SKGStressProjections
import SKGSectorSourceRepresentation
import SKGIndependentHamiltonPair
import SKGOriginalSourceAttachment

/-! Constraint-first composition. The complete accepted Kernel-faithful
Stage1 construction is retained before adding the actual same-action source.
All analytic endpoints are proofs; total metric stationarity occurs only
inside its conditional equation theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.CanonicalLicensing
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

structure SameActionKGSourceEndpoints (a : Parameters) (s kappa Lambda : ℝ) : Prop where
  retained_stage1 : CompleteKernelFaithfulCurvedKGEndpoints a s
  nonzero_coupling : kappa ≠ 0
  admitted_metric_rays : ∀ h : MetricSourceProbe (sourceDomain a), ∀ᶠ t : ℝ in 𝓝 0,
    scalarMetricRayOperand a h t ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
      ∀ p, (originalEHActMetric (scalarMetricRayOperand a h t) p).det < 0
  actual_metric_tangent : ∀ (h : MetricSourceProbe (sourceDomain a)) (p : CoordinatePoint) (i j : Fin 4),
    HasDerivAt (fun t => originalEHActMetric (scalarMetricRayOperand a h t) p i j) (tensorEncode (h p) i j) 0
  actual_matter_derivative : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a),
    HasDerivAt (scalarMetricRayAction a u protocol) (sameActionScalarMetricLF a u regular protocol.test) 0
  response_graph : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u)
    (h : MetricSourceProbe (sourceDomain a)) (y : ℝ), sameActionScalarMetricLF a u regular h = y ↔
      ∃ protocol : ScalarMetricRayProtocol a, scalarMetricRayIncidence a h protocol ∧ scalarMetricRayOutput a u protocol = y
  unique_actual_source : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u),
    ∃! T : SymmetricSourceComponents (sourceDomain a), ∀ protocol : ScalarMetricRayProtocol a,
      (1 / 2 : ℝ) * metricSourcePairing T protocol.test = scalarMetricRayOutput a u protocol
  response_lf_continuity : ∀ (u : CoordinatePoint → ℝ), ContDiff ℝ 2 u →
    Continuous (fun h : MetricSourceProbe (sourceDomain a) => scalarMetricRayOutput a u ⟨h⟩)
  actual_density_representation : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u)
    (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)), sameActionScalarSource a u regular i psi =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u)) i p * psi p
  source_reader_square : ∀ (state : RegularScalarSourceState a) (kind : ScalarSourceReaderKind)
    (h : MetricSourceProbe (sourceDomain a)), scalarSourceRawValue a state (.response kind h) =
      sameActionScalarMetricLF a state.localState.field (scalarSmoothTwo _ state.globalRegular) h
  smooth_stress : ∀ (u : CoordinatePoint → ℝ), ContDiff ℝ (⊤ : ℕ∞) u → ∀ i j,
    ContDiff ℝ (⊤ : ℕ∞) (fun p => sameSourceStress a u p i j)
  occupied_positive_stress : 0 < sameSourceStress a (occupiedSourceField a) 0 0 0
  occupied_actual_response : ∃ protocol : ScalarMetricRayProtocol a, scalarMetricRayOutput a (occupiedSourceField a) protocol ≠ 0
  off_shell_balance : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint), ContDiffAt ℝ 2 u p → ∀ b,
    coordinateDivergence (sourceMetric a) (sameSourceStress a u) p b =
      (scalarFieldWaveOperator (sourceMetric a) u p - massWaveNumber a ^ 2 * u p) * scalarPartial u p b
  constructed_conservation : ∀ (f h : CurvedCauchyDatum a) (p : CoordinatePoint), p ∈ sourceDomain a →
    coordinateDivergence (sourceMetric a) (sameSourceStress a (sourceField a f h)) p = 0
  actual_compact_ward : ∀ (f h : CurvedCauchyDatum a) (X : CoordinateVectorProbe (sourceDomain a)),
    HasDerivAt (scalarMetricRayAction a (sourceField a f h)
      ⟨compactMetricLieCLM (sourceDomain a) (sourceMetric a) (source_metric_smooth a) X⟩) 0 0
  action_sector_split : ∀ (u : CoordinatePoint → ℝ) (protocol : ScalarMetricRayProtocol a) (t : ℝ),
    scalarMetricRayAction a u protocol t = kineticScalarRayAction a u protocol t + massScalarRayAction a u protocol t
  actual_density_sector_split : ∀ (G : NativeRealMatrix) (v : Fin 4 → ℝ) (phi mu2 : ℝ),
    nativeRealClockDensity G v phi mu2 = nativeRealClockDensity G v phi 0 +
      (-(1 / 2 : ℝ) * nativeRealClockVolume G * mu2 * phi ^ 2)
  kinetic_actual_source : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u)
    (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)), representedMetricSource (kineticScalarMetricLF a u regular) i psi =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a) (kineticScalarStress a u)) i p * psi p
  mass_actual_source : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u)
    (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)), representedMetricSource (massScalarMetricLF a u (scalarSmoothTwo u regular)) i psi =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a) (massScalarStress a u)) i p * psi p
  sector_actual_derivatives : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a),
    HasDerivAt (kineticScalarRayAction a u protocol)
      ((1 / 2 : ℝ) * metricSourcePairing (representedMetricSource (kineticScalarMetricLF a u regular)) protocol.test) 0 ∧
    HasDerivAt (massScalarRayAction a u protocol)
      ((1 / 2 : ℝ) * metricSourcePairing (representedMetricSource (massScalarMetricLF a u regular)) protocol.test) 0
  off_shell_kinetic_balance : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint), ContDiffAt ℝ 2 u p → ∀ b,
    coordinateDivergence (sourceMetric a) (kineticScalarStress a u) p b = scalarFieldWaveOperator (sourceMetric a) u p * scalarPartial u p b
  off_shell_mass_balance : ∀ (u : CoordinatePoint → ℝ), ContDiff ℝ (⊤ : ℕ∞) u → ∀ p b,
    coordinateDivergence (sourceMetric a) (massScalarStress a u) p b = -scalarMassExchange a u p b
  opposite_on_shell_exchange : ∀ (f h : CurvedCauchyDatum a) (p : CoordinatePoint), p ∈ sourceDomain a → ∀ b,
    coordinateDivergence (sourceMetric a) (kineticScalarStress a (sourceField a f h)) p b = scalarMassExchange a (sourceField a f h) p b ∧
    coordinateDivergence (sourceMetric a) (massScalarStress a (sourceField a f h)) p b = -scalarMassExchange a (sourceField a f h) p b
  finite_balanced_registry : ∀ (m n : ℕ) (D residual external : Fin m → ℝ) (incidence : Fin m → Fin n → ℝ) (current : Fin n → ℝ),
    (∀ b, D b = residual b + external b + ∑ e, incidence b e * current e) →
    (∀ e, ∑ b, incidence b e = 0) → (∑ b, D b) = (∑ b, residual b) + ∑ b, external b
  same_lagrangian : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint), sameEHScalarDensity a u p =
    scalarCanonicalLagrangian (sourceFactor a p) (massWaveNumber a ^ 2) (u p) (scalarPartial u p 0) (fun i => scalarPartial u p i.succ)
  regular_legendre : ∀ (p : CoordinatePoint) (mu2 phi v pi : ℝ) (P : Fin 3 → ℝ),
    0 < deriv (fun w => deriv (fun z => scalarCanonicalLagrangian (sourceFactor a p) mu2 phi z P) w) v ∧
    scalarCanonicalVelocity (sourceFactor a p) (scalarCanonicalMomentum (sourceFactor a p) v) = v ∧
    scalarCanonicalMomentum (sourceFactor a p) (scalarCanonicalVelocity (sourceFactor a p) pi) = pi
  actual_legendre_hamiltonian : ∀ (p : CoordinatePoint) (mu2 phi pi : ℝ) (P : Fin 3 → ℝ),
    pi * scalarCanonicalVelocity (sourceFactor a p) pi -
      scalarCanonicalLagrangian (sourceFactor a p) mu2 phi (scalarCanonicalVelocity (sourceFactor a p) pi) P =
        scalarCanonicalHamiltonian (sourceFactor a p) mu2 phi pi P
  independent_hamilton_pair : ∀ (u pi : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u) (D : Opens CoordinatePoint),
    ScalarHamiltonPairOn a u pi D ↔ EqOn pi (actualScalarCanonicalMomentum a u) D ∧
      ∀ p ∈ D, scalarFieldWaveOperator (sourceMetric a) u p = massWaveNumber a ^ 2 * u p
  actual_spatial_variation : ∀ (u pi : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u)
    (t : ℝ) (d : KGSpatialSpace → ℝ), ContDiff ℝ (⊤ : ℕ∞) d → HasCompactSupport d →
    HasDerivAt (spatialHamiltonianRelative (scalarSpatialSlice (sourceFactor a) t)
      (scalarSpatialSlice u t) (scalarSpatialSlice pi t) d (massWaveNumber a ^ 2))
      (∫ x : KGSpatialSpace, actualScalarHamiltonianEuler a u (spaceTimePoint t x) * d x) 0
  same_stress_energy : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint),
    actualScalarHamiltonianDensity a u (actualScalarCanonicalMomentum a u) p = sourceFactor a p ^ 2 * scalarNormalEnergy a u p
  normal_is_unit : ∀ p : CoordinatePoint,
    coordinateMetricPairing (sourceMetric a p) (scalarSourceNormal a p) (scalarSourceNormal a p) = -1
  normal_energy_contraction : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint),
    scalarNormalEnergy a u p = ∑ i : Fin 4, ∑ j : Fin 4,
      scalarSourceNormal a p i * scalarSourceNormal a p j * sameSourceStress a u p i j
  normal_momentum_contraction : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint) (i : Fin 3),
    scalarNormalMomentum a u p i = -(∑ j : Fin 4, scalarSourceNormal a p j * sameSourceStress a u p j i.succ)
  hamiltonian_lapse : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint),
    actualScalarHamiltonianDensity a u (actualScalarCanonicalMomentum a u) p =
      scalarSourceLapse a p * (scalarSpatialVolume a p * scalarNormalEnergy a u p)
  same_stress_momentum : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint) (i : Fin 3),
    actualScalarCanonicalMomentum a u p * scalarPartial u p i.succ = -scalarSpatialVolume a p * scalarNormalMomentum a u p i
  spatial_stress_projection : ∀ (u : CoordinatePoint → ℝ) (p : CoordinatePoint) (i j : Fin 3),
    scalarSpatialStress a u p i j = scalarPartial u p i.succ * scalarPartial u p j.succ -
      (1 / 2 : ℝ) * sourceMetric a p i.succ j.succ *
        (scalarFieldKinetic (sourceMetric a) u p + massWaveNumber a ^ 2 * (u p * u p))
  physical_time : ∀ (u : CoordinatePoint → ℝ), ContDiff ℝ (⊤ : ℕ∞) u → ∀ t x,
    HasDerivAt (fun r => u (spaceTimePoint (a.speed * r) x)) (a.speed * scalarPartial u (spaceTimePoint (a.speed * t) x) 0) t
  actual_total_derivative : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a),
    HasDerivAt (sameTotalRayAction a kappa Lambda u protocol)
      (sameTotalMetricLF a kappa Lambda nonzero_coupling u regular protocol.test) 0
  derived_sourced_equation : ∀ (u : CoordinatePoint → ℝ), ContDiff ℝ (⊤ : ℕ∞) u →
    (SameTotalMetricStationary a kappa Lambda u ↔
      ∀ p ∈ sourceDomain a, sameEinsteinTensor a Lambda p = kappa • sameSourceStress a u p)
  actual_licensed_source_match : ∀ (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u),
    SameTotalMetricStationary a kappa Lambda u → ∀ (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)),
    restrictedEHKernelSource a s (⊤ : Opens CoordinatePoint) kappa Lambda nonzero_coupling
      (licensedEHSourceProfile a s (⊤ : Opens CoordinatePoint)
        (curvedLicensedMetricReceiver a s kappa Lambda nonzero_coupling)) i (liftSourceScalarTest a psi) =
      -sameActionScalarSource a u (scalarSmoothTwo u regular) i psi
  complete_original_record : ∀ (state : RegularScalarSourceState a)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint))) (program : List CurvedKGOperation)
    (questions : List (ScalarSourceQuestion a)),
    (licensedSameActionSourceRecord a s kappa Lambda nonzero_coupling state ops program questions).1 =
      licensedCurvedUseRecord a s kappa Lambda nonzero_coupling state.localState ops program
  original_record_square : ∀ (state : RegularScalarSourceState a)
    (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint))) (program : List CurvedKGOperation)
    (questions : List (ScalarSourceQuestion a)),
    licensedSameActionSourceRecord a s kappa Lambda nonzero_coupling state ops program questions =
      rawSameActionSourceRecord a s kappa Lambda state ops program questions
  attached_actual_readers : ∀ (state : RegularScalarSourceState a) (program : List CurvedKGOperation)
    (questions : List (ScalarSourceQuestion a)),
    (licensedSameActionSourceRecord a s kappa Lambda nonzero_coupling state [] program questions).2 =
      scalarSourceReadList a (sourceMetric a) state questions
  local_readers_and_failures : ∀ (metric : MetricField) (state other : RegularScalarSourceState a),
    ScalarUseSame a state.localState other.localState → ∀ questions : List (ScalarSourceQuestion a),
    scalarSourceReadList a metric state questions = scalarSourceReadList a metric other questions ∧
    firstScalarSourceFailure (scalarSourceReadList a metric state questions) =
      firstScalarSourceFailure (scalarSourceReadList a metric other questions)
  restriction_compatibility : ∀ (metric : MetricField) (state : RegularScalarSourceState a)
    (W : Opens CoordinatePoint) (inside : W ≤ state.localState.domain) (question : ScalarSourceQuestion a),
    sourceQuestionAllowed a (restrictScalarSourceState a state W inside) question →
    scalarSourceRead a metric (restrictScalarSourceState a state W inside) question = scalarSourceRead a metric state question
  continuation_square : ∀ (state : RegularScalarSourceState a) (request : ScalarContinuationRequest), request.scale ≠ 0 →
    ∀ inside : scalarContinuationDomain a request ≤ state.localState.domain,
    scalarContinuationDataMatch a state.localState request →
    ∀ (ops : List (PreparedHistoryOperation a (⊤ : Opens CoordinatePoint))) (program : List CurvedKGOperation)
    (questions : List (ScalarSourceQuestion a)),
    licensedSameActionSourceRecord a s kappa Lambda nonzero_coupling (continuedScalarSourceState a state request inside) ops program questions =
      licensedSameActionSourceRecord a s kappa Lambda nonzero_coupling
        (restrictScalarSourceState a state (scalarContinuationDomain a request) inside) ops program questions
  metric_change_failure : ∀ (metric : MetricField) (state : RegularScalarSourceState a) (question : ScalarSourceQuestion a),
    metric ≠ sourceMetric a → scalarSourceRead a metric state question = .error .incompatibleMetric
  domain_failure : ∀ (state : RegularScalarSourceState a) (question : ScalarSourceQuestion a),
    ¬sourceQuestionAllowed a state question → scalarSourceRead a (sourceMetric a) state question = .error .outsideDomain

theorem kernel_faithful_same_action_kg_source (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    SameActionKGSourceEndpoints a s kappa Lambda where
  retained_stage1 := kernel_faithful_same_eh_curved_kg_complete a s
  nonzero_coupling := coupling
  admitted_metric_rays := same_metric_ray_admitted_and_nondegenerate a
  actual_metric_tangent := same_metric_ray_actual_tangent a
  actual_matter_derivative := same_action_scalar_metric_derivative a
  response_graph := same_action_scalar_response_graph a
  unique_actual_source := same_action_scalar_actual_source_unique a
  response_lf_continuity := same_action_response_lf_continuous a
  actual_density_representation := same_action_source_represents_actual_stress a
  source_reader_square := scalar_source_reader_square a
  smooth_stress := same_source_stress_smooth a
  occupied_positive_stress := occupied_source_stress_positive a
  occupied_actual_response := occupied_actual_compact_metric_response a
  off_shell_balance := same_metric_scalar_stress_off_shell a
  constructed_conservation := constructed_scalar_stress_conserved a
  actual_compact_ward := actual_scalar_compact_lie_ray_stationary a
  action_sector_split := scalar_actual_action_kinetic_mass_split a
  actual_density_sector_split := scalar_actual_density_kinetic_mass_split
  kinetic_actual_source := kinetic_action_source_represents_actual_stress a
  mass_actual_source := mass_action_source_represents_actual_stress a
  sector_actual_derivatives := actual_sector_source_reader_square a
  off_shell_kinetic_balance := kinetic_scalar_off_shell_balance a
  off_shell_mass_balance := mass_scalar_actual_balance a
  opposite_on_shell_exchange := constructed_scalar_opposite_exchange a
  finite_balanced_registry := fun _ _ => finite_balanced_exchange_total
  same_lagrangian := same_density_scalar_canonical_lagrangian a
  regular_legendre := same_density_scalar_regular_legendre a
  actual_legendre_hamiltonian := fun p mu2 phi pi P => same_density_scalar_hamiltonian _ mu2 phi pi P (source_factor_nonzero a p)
  independent_hamilton_pair := independent_hamilton_pair_iff_same_kg a
  actual_spatial_variation := actual_scalar_spatial_hamiltonian_derivative a
  same_stress_energy := actual_scalar_hamiltonian_is_time_energy a
  normal_is_unit := scalar_source_normal_unit a
  normal_energy_contraction := scalar_normal_energy_is_actual_contraction a
  normal_momentum_contraction := scalar_normal_momentum_is_actual_contraction a
  hamiltonian_lapse := scalar_normal_hamiltonian_lapse a
  same_stress_momentum := scalar_canonical_momentum_projection a
  spatial_stress_projection := scalar_spatial_stress_projection a
  physical_time := scalar_physical_time_derivative a
  actual_total_derivative := same_total_ray_actual_derivative a kappa Lambda coupling
  derived_sourced_equation := actual_total_metric_stationarity_iff_sourced_einstein a kappa Lambda coupling
  actual_licensed_source_match := licensed_eh_receiver_is_negative_actual_matter_source a s kappa Lambda coupling
  complete_original_record := licensed_source_retains_complete_predecessor a s kappa Lambda coupling
  original_record_square := licensed_source_complete_record_square a s kappa Lambda coupling
  attached_actual_readers := licensed_source_empty_word_actual_readers a s kappa Lambda coupling
  local_readers_and_failures := scalar_source_records_and_failures_local a
  restriction_compatibility := scalar_source_restriction_compatibility a
  continuation_square := licensed_source_continuation_square a s kappa Lambda coupling
  metric_change_failure := scalar_source_metric_change_failed a
  domain_failure := scalar_source_outside_failed a

end AASCKleinGordon.SameActionSource
