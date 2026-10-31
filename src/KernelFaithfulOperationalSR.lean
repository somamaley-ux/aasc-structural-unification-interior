import OSRActualNetworkRadar
import OSRAffineFrameClosure
import OSRAffineFrames
import OSRArbitraryAxisMeasurement
import OSRAuxiliaryPassive
import OSRClockFrameTransport
import OSRClockLicensedSource
import OSRConnectedSynchronization
import OSRDirectionalClocks
import OSRFiniteNetworkCoverage
import OSRFrameSupply
import OSRFullObservationClosure
import OSRIdealResponse
import OSRInertialMeasurements
import OSRLicensedNetworkOperations
import OSRLocalRestLaw
import OSRMarkedComposition
import OSRMarkedStateTransport
import OSRMeasurementSourceClosure
import OSRMeasuringFrameSelection
import OSRMeasuringHyperplane
import OSRNativeIdealResponse
import OSRNetworkEvolution
import OSRNetworkLicensing
import OSRNetworkPassive
import OSRNetworkPopulation
import OSRNetworkSource
import OSRNetworkTransport
import OSRObservationPassive
import OSROccupiedIdealClass
import OSROccupiedRelay
import OSROccupiedRuler
import OSROldConsumerPassive
import OSRPhysicalUnits
import OSRPopulatedProtocol
import OSRProperRebaseTransport
import OSRProtocolDomains
import OSRRestNetwork
import OSRRestPresentation
import OSRRestrictedProtocol
import OSRRotatedMeasurement
import OSRTimelikeComparison
import KernelFaithfulRecoveryComparison
import KernelFaithfulNativeSREndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 15000000
open Set TopologicalSpace AASCSemanticExhaustion AASCMetricConstruction AASCMetricConstruction.SRIntegration
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
open scoped BigOperators InnerProductSpace
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace
structure KernelFaithfulOperationalSR (a : Parameters) (s kappa Lambda : ℝ) : Prop where
  retained_stage3 : RecoveryComparison.KernelFaithfulRecoveryComparison a s kappa Lambda
  retained_native_sr : ∀ Omega : Opens CoordinatePoint, KernelFaithfulNativeSREndpoints a s Omega
  receipt_recorded_delay_radar_derived_from_actual_null_legs : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (X Y : SRSpace)
    (tm ta td tp delay : ℝ)
    (incoming : ((ta,Y):SREvent)-(tm,X) ∈ srOriginalFutureRayIncrements)
    (outgoing : ((tp,X):SREvent)-(td,Y) ∈ srOriginalFutureRayIncrements)
    (recorded_wait : td-ta=delay),
    ta=(tm+tp-delay)/2 ∧ td=(tm+tp+delay)/2 ∧
      (tp-tm-delay)/2=‖Y-X‖
  receipt_every_successful_radar_answer_is_actual : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (index : ℕ) (correction : ℝ) (answer : RadarAnswer)
    (read : radarRead a s Omega n d index correction=some answer),
    ∃ r : ExchangeRequest n, d.schedule[index]?=some r ∧
      answer=actualRadarAnswer a s Omega n d index r ∧
      answer.offset=d.sites.phase r.toSite-d.sites.phase r.fromSite ∧
      answer.length=‖d.sites.position r.toSite-d.sites.position r.fromSite‖
  receipt_occupied_radar_path_sum_is_actual_phase_difference : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {d : NetworkData a s Omega n}
    (sound : networkSound a s Omega n d) {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j),
    occupiedRadarPathSum a s Omega n path=d.sites.phase j-d.sites.phase i
  receipt_every_occupied_radar_loop_sums_to_zero : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {d : NetworkData a s Omega n}
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (loop : OccupiedRadarPath a s Omega n d i i),
    occupiedRadarPathSum a s Omega n loop=0
  receipt_measured_ruler_answer_has_actual_simultaneous_events : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i j : Fin (n+1)) (T : ℝ)
    (domain : rulerDomain a s Omega n d i j T),
    ∃ X Y : SREvent, rulerRead a s Omega n d i j T=some (X,Y,‖Y.2-X.2‖) ∧ X.1=T ∧ Y.1=T
  receipt_actual_affine_identity : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (p : SREvent),
    frameEvent 1 0 p=p
  receipt_actual_affine_open_domain_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b : SREvent) (O : Set SREvent) (openDomain : IsOpen O),
    IsOpen (frameEvent A b '' O)
  receipt_actual_affine_inverse_is_the_inverse_frame : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b p : SREvent),
    frameInverse A b p=frameEvent A⁻¹ (-srMatrixFrameEventLinear A⁻¹ b) p
  receipt_frame_inverse_left : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b p : SREvent),
    frameInverse A b (frameEvent A b p)=p
  receipt_frame_inverse_right : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b p : SREvent),
    frameEvent A b (frameInverse A b p)=p
  receipt_frame_event_injective : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b : SREvent),
    Function.Injective (frameEvent A b)
  receipt_frame_event_composition : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A B : SRMatrixFrame) (a b p : SREvent),
    frameEvent A a (frameEvent B b p)=frameEvent (A*B) (frameEvent A a b) p
  receipt_frame_event_difference : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b p q : SREvent),
    frameEvent A b q-frameEvent A b p=srMatrixFrameEventLinear A (q-p)
  receipt_frame_preserves_actual_source_form : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (b p q : SREvent),
    srOriginalOrderQuadratic (frameEvent A b q-frameEvent A b p)=srOriginalOrderQuadratic (q-p)
  receipt_frame_barycentric : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b p q : SREvent) (t : ℝ),
    frameEvent A b ((1-t) • p+t • q)=(1-t) • frameEvent A b p+t • frameEvent A b q
  receipt_actual_segment_domain_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b p q : SREvent) (O : Set SREvent),
    segmentCovered (frameEvent A b '' O) (frameEvent A b p) (frameEvent A b q) ↔ segmentCovered O p q
  receipt_whole_affine_segments_populated : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (p q : SREvent),
    segmentCovered univ p q
  receipt_axis_boost_actually_admitted : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t),
    axisBoost Q t r hyper ∈ srNativeFrameComparisons
  receipt_actual_inverse_rotation_event : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (z : SREvent),
    srMatrixFrameEventLinear (srRestCoordinateUnit Q)⁻¹ z=(z.1,Q.symm z.2)
  receipt_actual_axis_boost_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (t r : ℝ) (hyper : t^2-r^2=1) (b z : SREvent),
    (frameEvent (axisBoost Q t r hyper) b z).1=t*z.1+r*(Q.symm z.2) 0+b.1
  receipt_actual_axis_selected_rest_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X : SRSpace),
    selectedSiteTime (axisBoost Q t r hyper) b T X=selectedRestTime t r b T (Q.symm X)
  receipt_arbitrary_axis_actual_measured_length : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X Y : SRSpace),
    ‖(measuredEndpoint (axisBoost Q t r hyper) b T Y).2-(measuredEndpoint (axisBoost Q t r hyper) b T X).2‖^2=
      ((Q.symm Y) 0-(Q.symm X) 0)^2/t^2+
      ((Q.symm Y) 1-(Q.symm X) 1)^2+((Q.symm Y) 2-(Q.symm X) 2)^2
  receipt_arbitrary_axis_actual_selected_time_gap : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X Y : SRSpace),
    selectedSiteTime (axisBoost Q t r hyper) b T Y-selectedSiteTime (axisBoost Q t r hyper) b T X=
      -(r/t)*((Q.symm Y) 0-(Q.symm X) 0)
  receipt_auxiliary_actual_clock_full_marked_state_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d)
    (r : ExchangeRequest n) (T : ℝ),
    let original : SRClockRecord := (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))
    let time := srPassiveMarkedTime a.mass d.frame d.origin original T
    srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n (passiveNetworkData a s Omega n B c d) r)
      (srPassiveMarkedTime a.mass (B*d.frame) (frameEvent B c d.origin) original T)=
    transportMarkedState a.mass B c time (srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n d r) time)
  receipt_native_frame_preserves_unit : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (U : SREvent) (unit : IsFutureUnit U),
    IsFutureUnit (srMatrixFrameEventLinear A U)
  receipt_directional_clock_marked_event : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ),
    srMarkedClockEvent mu0 (directionalClockUse mu0 J U origin phase T).record
      (directionalClockUse mu0 J U origin phase T).finish=origin+T • U
  receipt_directional_clock_actual_passive_state : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin b : SREvent) (phase : ℝ) (A : SRMatrixFrame),
    srPassiveClockState mu0 A b origin.1 (directionalClock mu0 J U origin.2 phase)=
      directionalClock mu0 J (srMatrixFrameEventLinear A U) (frameEvent A b origin).2 phase
  receipt_directional_clock_actual_passive_use : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin b : SREvent) (phase T : ℝ) (A : SRMatrixFrame),
    srPassiveClockUse mu0 A b (directionalClockUse mu0 J U origin phase T)=
      directionalClockUse mu0 J (srMatrixFrameEventLinear A U) (frameEvent A b origin) phase T
  receipt_directional_clock_actual_frame_readout : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (base : 0 < mu0) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin b : SREvent) (phase T : ℝ) (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons),
    srClockCertification mu0 (directionalClockUse mu0 J (srMatrixFrameEventLinear A U)
      (frameEvent A b origin) phase T)=srClockCertification mu0 (directionalClockUse mu0 J U origin phase T)
  receipt_directional_joint_actual_valid : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}),
    srNativeClockUseValid a.mass (directionalJointSource a s Omega J U origin phase T r H).clock
  receipt_licensed_directional_actual_source : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}),
    licensedJointSRSource a s Omega (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)=
      directionalJointSource a s Omega J U origin phase T r H
  receipt_licensed_directional_original_preparations : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}),
    licensedSRScalar a s Omega (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)=r ∧
      (licensedJointSRSource a s Omega (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)).metric=H
  receipt_directional_actual_canonical_license : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}),
    constructedLicensing (originalJointSRTask a s Omega)
      (directionalJointSource a s Omega J U origin phase T r H) (originalJointSRUseMeaning a s Omega)
  receipt_directional_actual_eh_operand : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (kappa Lambda : ℝ) (coupling : kappa ≠ 0),
    restrictedEHMetric a s Omega (licensedEHResponse a s Omega
      (licensedSRMetric a s Omega kappa Lambda coupling
        (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)))=
      originalEHActMetric H.val
  receipt_directional_actual_registered_reference : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (J : ℝ) (positive : 0 < a.mass+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (q : RegisteredQuestion (KGFamilyQuestion a Omega (kgOriginalObject a))),
    (licensedReadout a s Omega (licensedSRMetric a s Omega kappa Lambda coupling
      (licensedDirectionalClock a s Omega J positive U unit origin phase T forward r H)) []).answer
        (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q))=
      (licensedScalarReference a s Omega (scalarBaseObject a) r (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr
  receipt_actual_occupied_path_is_connected : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j),
    ActualRadarConnected a s Omega n d i j
  receipt_actual_undirected_component_synchronization_unique : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    {i j : Fin (n+1)} (connected : ActualRadarConnected a s Omega n d i j),
    other j-d.sites.phase j=other i-d.sites.phase i
  receipt_actual_undirected_component_has_one_common_origin : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    (base : Fin (n+1)),
    ∃ origin : ℝ, ∀ j, ActualRadarConnected a s Omega n d base j → other j=d.sites.phase j+origin
  receipt_directional_clock_actual_mass : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (U : SREvent) (x : SRSpace) (phase : ℝ),
    srNativeClockMass mu0 (directionalClock mu0 J U x phase)=mu0+J
  receipt_directional_clock_actual_hamiltonian : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase : ℝ),
    srNativeClockHamiltonian mu0 (directionalClock mu0 J U x phase)=(mu0+J)*U.1
  receipt_directional_clock_actual_proper_tangent : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase : ℝ),
    srNativeProperTangent mu0 (directionalClock mu0 J U x phase)=U
  receipt_directional_clock_actual_rate : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase : ℝ),
    srNativeClockRate mu0 (directionalClock mu0 J U x phase)=1/U.1
  receipt_directional_clock_actual_event : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase theta tau : ℝ),
    (theta+tau*U.1,(srNativeClockCoastFlow mu0 (tau*U.1) (directionalClock mu0 J U x phase)).position)=
      (theta,x)+tau • U
  receipt_directional_clock_actual_reading : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase tau : ℝ),
    (srNativeClockCoastFlow mu0 (tau*U.1) (directionalClock mu0 J U x phase)).reading=phase+tau
  receipt_directional_clock_use_actual_interval : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ),
    srNativeClockActualInterval mu0 (directionalClockUse mu0 J U origin phase T)=T
  receipt_directional_clock_use_actually_valid : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase T : ℝ) (forward : 0 ≤ T),
    srNativeClockUseValid mu0 (directionalClockUse mu0 J U origin phase T)
  receipt_directional_clock_complete_marked_record : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (origin : SREvent) (phase tau : ℝ) (id : Fin 2),
    let record := srNativeCoastingMarkedRecord mu0
      (id,origin.1,directionalClock mu0 J U origin.2 phase) (origin.1+tau*U.1)
    record.1=id ∧ record.2.position=origin.2+tau • U.2 ∧
      record.2.momentum=(mu0+J) • U.2 ∧ record.2.internalEnergy=J ∧ record.2.reading=phase+tau
  receipt_all_pairs_request_actually_registered : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (i j : Fin (n+1)),
    ∃ index : ℕ, (allPairsSchedule n)[index]?=some (⟨i,j,0,0,1⟩ : ExchangeRequest n)
  receipt_finite_all_pairs_network_is_actually_occupied : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phase : Fin (n+1) → ℝ),
    ∃ d : NetworkData a s Omega n, networkSound a s Omega n d ∧ d.sites.position=sites ∧ d.sites.phase=phase ∧
      ∀ i j, sites j ≠ sites i → ∃ index answer,
        d.schedule[index]?=some (⟨i,j,0,0,1⟩ : ExchangeRequest n) ∧
        radarRead a s Omega n d index 0=some answer ∧
        answer.offset=phase j-phase i ∧ answer.length=‖sites j-sites i‖
  receipt_synchronization_from_actual_successful_graph : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j),
    occupiedRadarPathSum a s Omega n path=other j-other i
  receipt_actual_component_synchronization_unique : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (other : Fin (n+1) → ℝ)
    (reads : ∀ index correction r answer, d.schedule[index]?=some r →
      radarRead a s Omega n d index correction=some answer → answer.offset=other r.toSite-other r.fromSite)
    {i j : Fin (n+1)} (path : OccupiedRadarPath a s Omega n d i j),
    other j-d.sites.phase j=other i-d.sites.phase i
  receipt_actual_radar_reversal_from_successful_records : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (p q : ExchangeRequest n) (i j : ℕ) (correctionP correctionQ : ℝ)
    (answerP answerQ : RadarAnswer) (regP : d.schedule[i]?=some p) (regQ : d.schedule[j]?=some q)
    (readP : radarRead a s Omega n d i correctionP=some answerP)
    (readQ : radarRead a s Omega n d j correctionQ=some answerQ)
    (fromEq : q.fromSite=p.toSite) (toEq : q.toSite=p.fromSite),
    answerQ.offset = -answerP.offset
  receipt_axial_boost_rest_vector : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyperbolic : t^2-r^2=1),
    srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) (1,0) =
      (t,r • srFirstSpatialUnit)
  receipt_proper_spatial_rotation_actually_supplied : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap = 1),
    srRestCoordinateUnit Q ∈ srNativeFrameComparisons
  receipt_actual_native_future_unit_frame_supply : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (U : SREvent) (unit : IsFutureUnit U),
    ∃ A : SRMatrixFrame, A ∈ srNativeFrameComparisons ∧
      srMatrixFrameEventLinear A (1,0) = U
  receipt_supplied_unit_frame_mem : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (U : SREvent) (unit : IsFutureUnit U),
    suppliedUnitFrame U unit ∈ srNativeFrameComparisons
  receipt_supplied_unit_frame_rest : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (U : SREvent) (unit : IsFutureUnit U),
    srMatrixFrameEventLinear (suppliedUnitFrame U unit) (1,0) = U
  receipt_auxiliary_endpoint_original_read_and_failure_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame)
    (admitted : B ∈ srNativeFrameComparisons) (c : SREvent) (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (index : ℕ) (r : ExchangeRequest n)
    (registered : d.schedule[index]?=some r) (T : ℝ),
    let original : SRClockRecord := (0,0,srNativeRestClock (relayZ (requestRelay a s Omega n d r)))
    let time := srPassiveMarkedTime a.mass d.frame d.origin original T
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.relayEndpoint index T)=
      (networkDataObserve a s Omega n d (.relayEndpoint index T)).map
        (fun answer => (answer.1,transportMarkedState a.mass B c time answer.2))
  receipt_unregistered_auxiliary_failure_retained : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (T : ℝ) (unregistered : d.schedule[index]?=none),
    networkDataObserve a s Omega n d (.relayEndpoint index T)=none ∧
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.relayEndpoint index T)=none
  receipt_original_coordinate_ruler_same_question_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (i j : Fin (n+1)) (T : ℝ),
    (measuringRead a s Omega n (passiveNetworkData a s Omega n B c d) ⟨d.frame,d.origin,T⟩ i j).map
      (fun answer => (answer.firstEvent,answer.secondEvent,answer.length))=
    (rulerRead a s Omega n d i j T).map
      (fun answer => (frameEvent B c answer.1,frameEvent B c answer.2.1,answer.2.2))
  receipt_site_event_and_reading_same_question_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (i : Fin (n+1)) (T : ℝ),
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.siteEvent i T)=
      frameEvent B c (networkDataObserve a s Omega n d (.siteEvent i T)) ∧
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.siteReading i T)=
      networkDataObserve a s Omega n d (.siteReading i T)
  receipt_full_licensed_operation_physical_refinement_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n)
    (r : LicensedNetworkReceiver a s Omega n),
    (licensedNetworkOperation a s Omega n op r).map (licensedNetworkToPhysical a s Omega n)=
      networkReceiverOperation a s Omega n op (licensedNetworkToPhysical a s Omega n r)
  receipt_rest_unit_is_future_unit : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), IsFutureUnit ((1:ℝ),(0:SRSpace))
  receipt_ideal_duration_zero : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : IdealInertialResponse),
    D.duration 0=0
  receipt_ideal_rest_response_derived : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : IdealInertialResponse) (t : ℝ) (inside : (t,0) ∈ D.certified),
    D.duration (t,0)=t
  receipt_ideal_inertial_response_classification : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : IdealInertialResponse)
    (w : SREvent) (inside : w ∈ D.certified) (future : IsFutureTimelike w),
    D.duration w=restLength w
  receipt_ideal_inertial_response_unique : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D E : IdealInertialResponse) (w : SREvent)
    (insideD : w ∈ D.certified) (insideE : w ∈ E.certified) (future : IsFutureTimelike w),
    D.duration w=E.duration w
  receipt_ideal_response_read_domain : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : IdealInertialResponse) (w : SREvent),
    (idealResponseRead D w).isSome=true ↔ w ∈ D.certified
  receipt_gamma_positive_and_hyperbolic : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (beta : ℝ) (subluminal : beta^2 < 1),
    0 < lorentzGamma beta ∧ (lorentzGamma beta)^2-(lorentzGamma beta*beta)^2=1
  receipt_measurement_boost_actually_supplied : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (beta : ℝ) (subluminal : beta^2 < 1),
    measurementBoost beta subluminal ∈ srNativeFrameComparisons
  receipt_axial_boost_spatial_components : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyper : t^2-r^2=1) (z : SREvent),
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) z).2 0=r*z.1+t*z.2 0 ∧
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) z).2 1=z.2 1 ∧
    (srMatrixFrameEventLinear (srUnitAxialBoost t r hyper) z).2 2=z.2 2
  receipt_endpoint_selection_is_simultaneous_and_unique : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X : SRSpace),
    (selectedEndpoint t r hyper b T X).1=T ∧
    ∀ u : ℝ, (frameEvent (srUnitAxialBoost t r hyper) b (u,X)).1=T → u=selectedRestTime t r b T X
  receipt_actual_selected_endpoint_separation : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X Y : SRSpace),
    let delta := (selectedEndpoint t r hyper b T Y).2-(selectedEndpoint t r hyper b T X).2
    delta 0=(Y 0-X 0)/t ∧ delta 1=Y 1-X 1 ∧ delta 2=Y 2-X 2 ∧
    selectedRestTime t r b T Y-selectedRestTime t r b T X=-(r/t)*(Y 0-X 0)
  receipt_actual_selected_length_squared : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X Y : SRSpace),
    ‖(selectedEndpoint t r hyper b T Y).2-(selectedEndpoint t r hyper b T X).2‖^2=
      (Y 0-X 0)^2/t^2+(Y 1-X 1)^2+(Y 2-X 2)^2
  receipt_measurement_selected_rest_time_gap : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (beta : ℝ) (subluminal : beta^2 < 1)
    (b : SREvent) (T : ℝ) (X Y : SRSpace),
    selectedRestTime (lorentzGamma beta) (lorentzGamma beta*beta) b T Y-
      selectedRestTime (lorentzGamma beta) (lorentzGamma beta*beta) b T X=-beta*(Y 0-X 0)
  receipt_fixed_event_pair_passive_simultaneity : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyper : t^2-r^2=1)
    (p q : SREvent) (simultaneous : p.1=q.1),
    (srMatrixFrameEventLinear (srUnitAxialBoost t (-r) (by nlinarith)) q).1-
      (srMatrixFrameEventLinear (srUnitAxialBoost t (-r) (by nlinarith)) p).1=-r*(q.2 0-p.2 0)
  receipt_same_bearer_ticks_actual_dilation : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positiveMass : 0 < mu0+S.internalEnergy i) (t r : ℝ) (hyper : t^2-r^2=1)
    (b : SREvent) (u v : ℝ),
    (frameEvent (srUnitAxialBoost t r hyper) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) v)).1-
      (frameEvent (srUnitAxialBoost t r hyper) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) u)).1=
    t*((srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) v).2.reading-
      (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) u).2.reading)
  receipt_actual_orientation_preserves_measured_length : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (x y : SRSpace),
    ‖Q y-Q x‖=‖y-x‖
  receipt_physical_time_adapter_inverse : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (c : ℝ) (positive : 0 < c) (p : SREvent),
    ((physicalEvent c p).1/c,(physicalEvent c p).2)=p
  receipt_licensed_network_operation_actual_source_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n) (r : LicensedNetworkReceiver a s Omega n),
    (licensedNetworkOperation a s Omega n op r).map (licensedNetworkSource a s Omega n)=
      networkOperation a s Omega n op (licensedNetworkSource a s Omega n r)
  receipt_licensed_network_operation_actual_readout_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n)
    (r : LicensedNetworkReceiver a s Omega n) (q : NetworkContext n),
    (licensedNetworkOperation a s Omega n op r).map (fun next => licensedNetworkObserve a s Omega n next q)=
      (networkOperation a s Omega n op (licensedNetworkSource a s Omega n r)).map
        (fun next => networkCompleteObserve a s Omega n next q)
  receipt_licensed_network_operation_domain_is_exact : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n) (r : LicensedNetworkReceiver a s Omega n),
    (licensedNetworkOperation a s Omega n op r).isSome=
      (networkOperation a s Omega n op (licensedNetworkSource a s Omega n r)).isSome
  receipt_licensed_network_full_finite_first_failure_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (ops : List (NetworkOperation n))
    (r : LicensedNetworkReceiver a s Omega n),
    licensedNetworkFirstFailure a s Omega n ops r=networkFirstFailure a s Omega n ops (licensedNetworkSource a s Omega n r)
  receipt_licensed_network_passive_source_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n),
    licensedNetworkSource a s Omega n (licensedNetworkPassive a s Omega n B admitted c r)=
      passiveNetwork a s Omega n B c (licensedNetworkSource a s Omega n r)
  receipt_licensed_network_passive_full_first_failure : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (ops : List (NetworkOperation n)) (r : LicensedNetworkReceiver a s Omega n),
    licensedNetworkFirstFailure a s Omega n
      (ops.map (passiveNetworkOperation a s Omega n (licensedNetworkSource a s Omega n r).data))
      (licensedNetworkPassive a s Omega n B admitted c r)=licensedNetworkFirstFailure a s Omega n ops r
  receipt_selected_network_event_and_reading_are_actual : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)),
    let time := srPassiveMarkedTime a.mass x.data.frame x.data.origin (siteRecord a.mass x.data.sites i) x.data.reference
    srMarkedClockEvent a.mass (networkRawJoint a s Omega n x i).clock.record time=selectedNetworkEvent a s Omega n x i ∧
    (srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record time).2.reading=
      selectedNetworkReading a s Omega n x i
  receipt_actual_reference_advance_selected_event_and_reading : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)) (delta : ℝ) (forward : 0 ≤ delta),
    let y : NetworkSource a s Omega n := {x with data := {x.data with reference := x.data.reference+delta}}
    selectedNetworkEvent a s Omega n y i=frameEvent x.data.frame x.data.origin
      (x.data.reference+delta,x.data.sites.position i) ∧
    selectedNetworkReading a s Omega n y i=x.data.sites.phase i+x.data.reference+delta ∧
    networkOperation a s Omega n (.advance delta) x=some y
  receipt_local_rest_response_zero : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : LocalRestLaw),
    D.response 0 = 0
  receipt_local_rest_response_monotone : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : LocalRestLaw),
    MonotoneOn D.response D.domain
  receipt_local_rest_response_nsmul : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : LocalRestLaw) (n : ℕ) (x : ℝ)
    (positive : 0 ≤ x) (inside : (n:ℝ)*x ∈ D.domain),
    D.response ((n:ℝ)*x) = (n:ℝ)*D.response x
  receipt_calibrated_rest_grid_error : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : LocalRestLaw) (T : ℝ)
    (positive : 0 < T) (calibratedDomain : T ∈ D.domain) (calibrated : D.response T=T)
    (r : ℝ) (inside : r ∈ D.domain) (n : ℕ) (hn : 0 < n),
    |D.response r-r| ≤ T/(n:ℝ)
  receipt_calibrated_local_rest_response_unique : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (D : LocalRestLaw) (T : ℝ)
    (positive : 0 < T) (calibratedDomain : T ∈ D.domain) (calibrated : D.response T=T)
    (r : ℝ) (inside : r ∈ D.domain),
    D.response r=r
  receipt_passive_full_marked_state_composition : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) (base : 0 < mu0)
    (B A : SRMatrixFrame) (admittedB : B ∈ srNativeFrameComparisons)
    (admittedA : A ∈ srNativeFrameComparisons) (c b : SREvent)
    (record : SRClockRecord) (positive : 0 < srNativeClockMass mu0 record.2.2) (T : ℝ),
    srNativeCoastingMarkedRecord mu0
      (srPassiveClockRecord mu0 (B*A) (srMatrixFrameEventLinear B b+c) record)
      (srPassiveMarkedTime mu0 (B*A) (srMatrixFrameEventLinear B b+c) record T)=
    transportMarkedState mu0 B c (srPassiveMarkedTime mu0 A b record T)
      (srNativeCoastingMarkedRecord mu0 (srPassiveClockRecord mu0 A b record)
        (srPassiveMarkedTime mu0 A b record T))
  receipt_passive_full_marked_state_is_actual : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) (base : 0 < mu0)
    (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons) (c : SREvent)
    (record : SRClockRecord) (positive : 0 < srNativeClockMass mu0 record.2.2) (time : ℝ),
    srNativeCoastingMarkedRecord mu0 (srPassiveClockRecord mu0 B c record) (srPassiveMarkedTime mu0 B c record time)=
      transportMarkedState mu0 B c time (srNativeCoastingMarkedRecord mu0 record time)
  receipt_retained_measuring_answer_is_same_actual_clock : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (Q : MeasuringQuery) (i j : Fin (n+1)),
    let answer := actualMeasuringAnswer a s Omega n d Q i j
    let ti := srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i) (measuringSiteTime Q (d.sites.position i))
    let tj := srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites j) (measuringSiteTime Q (d.sites.position j))
    answer.firstEvent=srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d i).clock.record ti ∧
    answer.secondEvent=srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d j).clock.record tj ∧
    answer.firstReading=(srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n d i).clock.record ti).2.reading ∧
    answer.secondReading=(srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n d j).clock.record tj).2.reading
  receipt_original_coordinate_ruler_is_retained_query_specialization : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (i j : Fin (n+1)) (T : ℝ),
    rulerRead a s Omega n d i j T=
      (measuringRead a s Omega n d ⟨d.frame,d.origin,T⟩ i j).map
        (fun answer => (answer.firstEvent,answer.secondEvent,answer.length))
  receipt_licensed_measuring_read_same_question_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)),
    licensedNetworkObserve a s Omega n (licensedNetworkPassive a s Omega n B admitted c r)
      (.original (.measuring Q i j))=
      (licensedNetworkObserve a s Omega n r (.original (.measuring Q i j))).map (transportMeasuringAnswer B c)
  receipt_registered_protocol_ledger_is_exactly_retained : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n),
    networkCompleteObserve a s Omega n x (.original .protocolContext)=
      (x.data.schedule,x.data.clockResource,x.data.signalResource,x.data.relayResource)
  receipt_observer_slope_actually_positive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons),
    0 < observerSlope A
  receipt_actual_site_event_affine_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b : SREvent) (u : ℝ) (X : SRSpace),
    (frameEvent A b (u,X)).1=(frameEvent A b (0,X)).1+u*observerSlope A
  receipt_measuring_frame_selected_events_actual_and_unique : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) (b : SREvent) (T : ℝ) (X : SRSpace),
    (measuredEndpoint A b T X).1=T ∧
    ∀ u : ℝ, (frameEvent A b (u,X)).1=T → u=selectedSiteTime A b T X
  receipt_general_selection_is_actual_axial_selection : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X : SRSpace),
    measuredEndpoint (srUnitAxialBoost t r hyper) b T X=selectedEndpoint t r hyper b T X
  receipt_same_measuring_hyperplane_is_actually_transported : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A B : SRMatrixFrame) (b c : SREvent) (Q : MeasuringQuery),
    presentedMeasuringHyperplane (B*A) (frameEvent B c b) Q=
      frameEvent B c '' presentedMeasuringHyperplane A b Q
  receipt_measured_endpoint_lies_on_retained_hyperplane : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : MeasuringQuery)
    (admitted : Q.frame ∈ srNativeFrameComparisons) (X : SRSpace),
    ((measuringSiteTime Q X,X):SREvent) ∈ measuringHyperplane Q
  receipt_presented_selected_event_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A B : SRMatrixFrame) (b c : SREvent)
    (Q : MeasuringQuery) (X : SRSpace),
    frameEvent (B*A) (frameEvent B c b) (measuringSiteTime Q X,X)=
      frameEvent B c (frameEvent A b (measuringSiteTime Q X,X))
  receipt_native_duration_zero : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ),
    nativeDuration mu0 J 0=0
  receipt_native_duration_is_actual_metric_length : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (w : SREvent) (future : IsFutureTimelike w),
    nativeDuration mu0 J w=restLength w
  receipt_native_duration_unit_scale : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (t : ℝ) (forward : 0 ≤ t),
    nativeDuration mu0 J (t • U)=t
  receipt_native_certified_frame : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons) (w : SREvent),
    w ∈ nativeCertified ↔ srMatrixFrameEventLinear A w ∈ nativeCertified
  receipt_native_duration_same_event_frame : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons) (w : SREvent) (inside : w ∈ nativeCertified),
    nativeDuration mu0 J (srMatrixFrameEventLinear A w)=nativeDuration mu0 J w
  receipt_native_duration_has_actual_original_use : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (w : SREvent) (future : IsFutureTimelike w),
    srNativeClockUseValid mu0 (nativeIntervalUse mu0 J w) ∧
      srNativeClockActualInterval mu0 (nativeIntervalUse mu0 J w)=nativeDuration mu0 J w ∧
      srMarkedClockEvent mu0 (nativeIntervalUse mu0 J w).record (nativeIntervalUse mu0 J w).finish=w
  receipt_native_interval_use_is_same_passively_transported_clock : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ)
    (positive : 0 < mu0+J) (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) (future : IsFutureTimelike w),
    nativeIntervalUse mu0 J (srMatrixFrameEventLinear A w)=
      srPassiveClockUse mu0 A 0 (nativeIntervalUse mu0 J w)
  receipt_network_data_operation_retains_actual_records : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n)
    (d e : NetworkData a s Omega n) (step : networkDataOperation a s Omega n op d=some e) (i : Fin (n+1)),
    (networkBaseJoint a s Omega n e i).clock.record=(networkBaseJoint a s Omega n d i).clock.record
  receipt_network_raw_record_is_same_marked_history : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n) (i : Fin (n+1)) (t : ℝ),
    srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record t=
      srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n x.data i).clock.record t
  receipt_network_all_successful_operations_retain_underlying_histories : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n)
    (x y : NetworkSource a s Omega n) (step : networkOperation a s Omega n op x=some y)
    (i : Fin (n+1)) (t : ℝ),
    srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n y i).clock.record t=
      srNativeCoastingMarkedRecord a.mass (networkRawJoint a s Omega n x i).clock.record t
  receipt_site_window_extension_is_actual_old_extension : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {k : ℕ} (S : SiteData k)
    (i : Fin (k+1)) (positive : 0 < mu0+S.internalEnergy i) (lo hi delta : ℝ),
    siteUse mu0 S i lo (hi+delta)=srNativeExtendClockUse mu0 delta (siteUse mu0 S i lo hi)
  receipt_network_window_extension_has_actual_coordinate_slope : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (delta : ℝ),
    (networkBaseJoint a s Omega n {d with hi := d.hi+delta} i).clock=
      srNativeExtendClockUse a.mass
        (srPassiveClockSlope a.mass d.frame (siteRecord a.mass d.sites i).2.2*delta)
        (networkBaseJoint a s Omega n d i).clock
  receipt_network_nonnegative_reference_advance_is_actual : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n) (delta : ℝ)
    (forward : 0 ≤ delta),
    networkOperation a s Omega n (.advance delta) x=some {x with data := {x.data with reference := x.data.reference+delta}}
  receipt_network_continuation_selection_exit_is_retained : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n) (delta : ℝ)
    (forward : 0 ≤ delta) (exit : x.data.hi < x.data.reference+delta),
    networkCompleteObserve a s Omega n x (.domain (.advance delta))=true ∧
    networkCompleteObserve a s Omega n x (.after (.advance delta) (.original .referenceSelection))=
      some (x.data.reference+delta,false)
  receipt_network_receiver_operation_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n) (x : NetworkSource a s Omega n),
    networkReceiverOperation a s Omega n op (presentNetwork a s Omega n x)=
      (networkOperation a s Omega n op x).map (presentNetwork a s Omega n)
  receipt_network_finite_first_failure_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (ops : List (NetworkOperation n)) (x : NetworkSource a s Omega n),
    networkReceiverFirstFailure a s Omega n ops (presentNetwork a s Omega n x)=networkFirstFailure a s Omega n ops x
  receipt_licensed_network_same_metric_operand : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedNetworkReceiver a s Omega n)
    (i : Fin (n+1)) (kappa Lambda : ℝ) (coupling : kappa ≠ 0),
    restrictedEHMetric a s Omega (licensedEHResponse a s Omega (licensedSRMetric a s Omega kappa Lambda coupling
      (licensedNetworkToOld a s Omega n r i)))=originalEHActMetric (licensedNetworkSource a s Omega n r).data.metric.val
  receipt_licensed_network_complete_registered_reference : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedNetworkReceiver a s Omega n)
    (i : Fin (n+1)) (kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (q : RegisteredQuestion (KGFamilyQuestion a Omega (kgOriginalObject a))),
    (licensedReadout a s Omega (licensedSRMetric a s Omega kappa Lambda coupling (licensedNetworkToOld a s Omega n r i)) []).answer
      (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q))=
    (licensedScalarReference a s Omega (scalarBaseObject a) (licensedNetworkSource a s Omega n r).data.scalar
      (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr
  receipt_network_rebase_preserves_complete_profile : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (h : Fin (n+1) → ℝ) (x : NetworkSource a s Omega n),
    networkCompleteObserve a s Omega n (networkRebase a s Omega n h x)=networkCompleteObserve a s Omega n x
  receipt_network_data_operation_preserves_sound : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n) (d e : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (step : networkDataOperation a s Omega n op d=some e),
    networkSound a s Omega n e
  receipt_network_operation_preserves_actual_sound_region : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n)
    (x y : NetworkSource a s Omega n) (sound : networkSound a s Omega n x.data)
    (step : networkOperation a s Omega n op x=some y),
    networkSound a s Omega n y.data
  receipt_network_actual_source_passes_local_tests : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data),
    originalLocalTest (networkTask a s Omega n) x
  receipt_network_actual_sound_region_postfixed : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), networkSoundRegion a s Omega n ⊆ originalSafetyOperator (networkTask a s Omega n) (networkSoundRegion a s Omega n)
  receipt_actual_network_source_has_kernel_faithful_license : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data),
    constructedLicensing (networkTask a s Omega n) x (networkMeaning a s Omega n)
  receipt_licensed_network_has_actual_sound_source : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedNetworkReceiver a s Omega n),
    networkSound a s Omega n (licensedNetworkSource a s Omega n r).data
  receipt_licensed_network_old_actual_raw_source_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)),
    licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n (presentLicensedNetwork a s Omega n x sound) i)=
      networkRawJoint a s Omega n x i
  receipt_licensed_network_old_preparations_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedNetworkReceiver a s Omega n) (i : Fin (n+1)),
    licensedSRScalar a s Omega (licensedNetworkToOld a s Omega n r i)=(licensedNetworkSource a s Omega n r).data.scalar ∧
    (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).metric=(licensedNetworkSource a s Omega n r).data.metric
  receipt_passive_network_actually_sound : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d),
    networkSound a s Omega n (passiveNetworkData a s Omega n B c d)
  receipt_inverse_chart_after_actual_presentation : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A B : SRMatrixFrame) (b c p : SREvent),
    frameInverse (B*A) (frameEvent B c b) (frameEvent B c p)=frameInverse A b p
  receipt_inverse_chart_domain_image : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A B : SRMatrixFrame) (b c : SREvent) (O : Set SREvent),
    frameInverse (B*A) (frameEvent B c b) '' (frameEvent B c '' O)=frameInverse A b '' O
  receipt_passive_network_request_domain : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (correction : ℝ),
    requestDomain a s Omega n (passiveNetworkData a s Omega n B c d) index correction ↔
      requestDomain a s Omega n d index correction
  receipt_passive_network_measuring_domain : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)),
    measuringDomain a s Omega n (passiveNetworkData a s Omega n B c d) Q i j ↔
      measuringDomain a s Omega n d Q i j
  receipt_actual_measuring_answer_same_question_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)),
    actualMeasuringAnswer a s Omega n (passiveNetworkData a s Omega n B c d) Q i j=
      transportMeasuringAnswer B c (actualMeasuringAnswer a s Omega n d Q i j)
  receipt_measuring_read_same_question_transport_and_failure : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (Q : MeasuringQuery) (i j : Fin (n+1)),
    measuringRead a s Omega n (passiveNetworkData a s Omega n B c d) Q i j=
      (measuringRead a s Omega n d Q i j).map (transportMeasuringAnswer B c)
  receipt_network_partial_operation_passive_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (op : NetworkOperation n) (x : NetworkSource a s Omega n),
    networkOperation a s Omega n (passiveNetworkOperation a s Omega n x.data op) (passiveNetwork a s Omega n B c x)=
      (networkOperation a s Omega n op x).map (passiveNetwork a s Omega n B c)
  receipt_network_operation_retains_presentation : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n)
    (d e : NetworkData a s Omega n) (step : networkDataOperation a s Omega n op d=some e),
    e.frame=d.frame ∧ e.origin=d.origin
  receipt_passive_program_parameter_stable : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n) (x y : NetworkSource a s Omega n)
    (step : networkOperation a s Omega n op x=some y),
    passiveNetworkOperation a s Omega n y.data=passiveNetworkOperation a s Omega n x.data
  receipt_passive_network_finite_first_failure : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (ops : List (NetworkOperation n)) (x : NetworkSource a s Omega n),
    networkFirstFailure a s Omega n (ops.map (passiveNetworkOperation a s Omega n x.data))
      (passiveNetwork a s Omega n B c x)=networkFirstFailure a s Omega n ops x
  receipt_populated_network_actual_sound : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ) (ordered : lo ≤ hi)
    (schedule : List (ExchangeRequest n)),
    networkSound a s Omega n (populatedNetworkData a s Omega n r H sites phases lo hi schedule)
  receipt_inhabited_network_covers_every_old_preparation : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ) (ordered : lo ≤ hi)
    (schedule : List (ExchangeRequest n)),
    ∃ receiver : LicensedNetworkReceiver a s Omega n, ∀ i : Fin (n+1),
      licensedSRScalar a s Omega (licensedNetworkToOld a s Omega n receiver i)=r ∧
      (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n receiver i)).metric=H
  receipt_network_base_joint_actually_valid : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d)
    (i : Fin (n+1)),
    srNativeClockUseValid a.mass (networkBaseJoint a s Omega n d i).clock
  receipt_network_raw_joint_actually_valid : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)),
    srNativeClockUseValid a.mass (networkRawJoint a s Omega n x i).clock
  receipt_network_licensed_site_retains_actual_raw_source : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)),
    licensedJointSRSource a s Omega (licensedNetworkSite a s Omega n x sound i)=networkRawJoint a s Omega n x i
  receipt_radar_read_exact_domain : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n) (index : ℕ) (correction : ℝ),
    (radarRead a s Omega n d index correction).isSome=true ↔ requestDomain a s Omega n d index correction
  receipt_occupied_network_radar_answer : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n) (sound : networkSound a s Omega n d)
    (index : ℕ) (r : ExchangeRequest n),
    (actualRadarAnswer a s Omega n d index r).offset=d.sites.phase r.toSite-d.sites.phase r.fromSite ∧
    (actualRadarAnswer a s Omega n d index r).length=‖d.sites.position r.toSite-d.sites.position r.fromSite‖
  receipt_relay_extra_endpoint_is_actual_positive_clock : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n) (r : ExchangeRequest n),
    0 < srNativeClockMass a.mass (srNativeRestClock (relayZ (requestRelay a s Omega n d r))) ∧
    ∀ T : ℝ, (srNativeClockCoastFlow a.mass T
      (srNativeRestClock (relayZ (requestRelay a s Omega n d r)))).reading=T
  receipt_network_operation_actual_data_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n) (x : NetworkSource a s Omega n),
    (networkOperation a s Omega n op x).map NetworkSource.data=networkDataOperation a s Omega n op x.data
  receipt_network_complete_profile_factors_physical_data : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (q : SRContextQuery (NetworkQuestion n) (NetworkOperation n)),
    networkCompleteObserve a s Omega n x q=networkDataCompleteObserve a s Omega n x.data q
  receipt_network_actual_raw_old_profile_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n) (i : Fin (n+1)) (q : JointContext),
    networkCompleteObserve a s Omega n x (.original (.old i q))=
      jointCompleteObserve a s Omega (networkRawJoint a s Omega n x i) q
  receipt_network_old_physical_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n) (i : Fin (n+1)),
    networkToOldPhysical a s Omega n i (presentNetwork a s Omega n x)=
      presentJointOriginal a s Omega (networkRawJoint a s Omega n x i)
  receipt_network_all_registered_operations_have_exact_descent : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (op : NetworkOperation n),
    ∃! reduced : NetworkReceiver a s Omega n → Option (NetworkReceiver a s Omega n),
      ∀ x, reduced (presentNetwork a s Omega n x)=
        (networkOperation a s Omega n op x).map (presentNetwork a s Omega n)
  receipt_network_failed_radar_attempt_is_retained : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n) (index : ℕ) (correction : ℝ)
    (failed : ¬ requestDomain a s Omega n x.data index correction),
    networkCompleteObserve a s Omega n x (.domain (.certifyRadar index correction))=false ∧
    networkCompleteObserve a s Omega n x (.after (.certifyRadar index correction) (.original .referenceSelection))=none
  receipt_raw_network_clock_actual_same_event : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (t : ℝ),
    srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d i).clock.record
      (srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i) t)=
      frameEvent d.frame d.origin (t,d.sites.position i)
  receipt_raw_network_clock_actual_same_reading : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (t : ℝ),
    (srNativeCoastingMarkedRecord a.mass (networkBaseJoint a s Omega n d i).clock.record
      (srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i) t)).2.reading=
      siteReading a.mass d.sites i t
  receipt_measured_network_endpoints_are_actual_same_clocks : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (i : Fin (n+1)) (T : ℝ),
    srMarkedClockEvent a.mass (networkBaseJoint a s Omega n d i).clock.record
      (srPassiveMarkedTime a.mass d.frame d.origin (siteRecord a.mass d.sites i)
        (selectedSiteTime d.frame d.origin T (d.sites.position i)))=
      measuredEndpoint d.frame d.origin T (d.sites.position i)
  receipt_relay_extra_endpoint_actual_passive_event_and_reading : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (d : NetworkData a s Omega n)
    (sound : networkSound a s Omega n d) (r : ExchangeRequest n) (T : ℝ),
    let R := requestRelay a s Omega n d r
    let original : SRClockRecord := (0,0,srNativeRestClock (relayZ R))
    srMarkedClockEvent a.mass (relayClockRecord a s Omega n d r)
      (srPassiveMarkedTime a.mass d.frame d.origin original T)=frameEvent d.frame d.origin (T,relayZ R) ∧
    (srNativeCoastingMarkedRecord a.mass (relayClockRecord a s Omega n d r)
      (srPassiveMarkedTime a.mass d.frame d.origin original T)).2.reading=T
  receipt_actual_radar_answer_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent) (d : NetworkData a s Omega n)
    (index : ℕ) (r : ExchangeRequest n),
    actualRadarAnswer a s Omega n (passiveNetworkData a s Omega n B c d) index r=
      transportRadarAnswer B c (actualRadarAnswer a s Omega n d index r)
  receipt_actual_radar_read_and_failure_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent) (d : NetworkData a s Omega n)
    (index : ℕ) (correction : ℝ),
    radarRead a s Omega n (passiveNetworkData a s Omega n B c d) index correction=
      (radarRead a s Omega n d index correction).map (transportRadarAnswer B c)
  receipt_actual_signal_ledger_events_momenta_identities_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (r : ExchangeRequest n) (T : ℝ),
    signalLedger a s Omega n (passiveNetworkData a s Omega n B c d) index r T=
      transportSignalLedger B c (signalLedger a s Omega n d index r T)
  receipt_signal_read_and_failure_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n) (index : ℕ) (T : ℝ),
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) (.signal index T)=
      (networkDataObserve a s Omega n d (.signal index T)).map (transportSignalLedger B c)
  receipt_protocol_and_reference_are_retained_under_passive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (c : SREvent)
    (d : NetworkData a s Omega n),
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) .protocolContext=
      networkDataObserve a s Omega n d .protocolContext ∧
    networkDataObserve a s Omega n (passiveNetworkData a s Omega n B c d) .referenceSelection=
      networkDataObserve a s Omega n d .referenceSelection
  receipt_actual_native_ideal_class_is_occupied : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (base : 0 < mu0) (positive : 0 < mu0+J),
    ∃ D : IdealInertialResponse, D.duration=nativeDuration mu0 J ∧ D.certified=nativeCertified ∧
      ∀ w : SREvent, w ∈ D.certified → IsFutureTimelike w →
        D.duration w=restLength w ∧ srNativeClockUseValid mu0 (nativeIntervalUse mu0 J w) ∧
        srNativeClockActualInterval mu0 (nativeIntervalUse mu0 J w)=D.duration w ∧
        srMarkedClockEvent mu0 (nativeIntervalUse mu0 J w).record (nativeIntervalUse mu0 J w).finish=w
  receipt_relay_main_crossing_records : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData) (length : 0 < R.length) (delay : 0 ≤ R.delay),
    relayMainPosition R (relayDeparture R).1=R.X ∧
    relayMainPosition R (relayArrival R).1=relayY R ∧
    relayMainPosition R (relayTurn R).1=relayZ R ∧
    relayMainPosition R (relayRelease R).1=relayY R ∧
    relayMainPosition R (relayReturn R).1=R.X
  receipt_relay_compensator_shared_vertex : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData),
    relayCompensatorPosition R (relayTurn R).1=relayZ R
  receipt_relay_full_legs_are_actual_original_rays : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData) (length : 0 < R.length)
    (delay : 0 ≤ R.delay) (unit : ‖R.direction‖=1),
    relayTurn R-relayDeparture R ∈ srOriginalFutureRayIncrements ∧
    relayReturn R-relayTurn R ∈ srOriginalFutureRayIncrements
  receipt_relay_positive_energy_and_balanced_vertex : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData) (energy : 0 < R.energy)
    (unit : ‖R.direction‖=1) (mu : ℝ),
    srNativePositiveRayMomentum R.energy R.direction ∈ srOriginalFutureRayIncrements ∧
    srNativePositiveRayMomentum R.energy (-R.direction) ∈ srOriginalFutureRayIncrements ∧
    ((mu,(0:SRSpace))+srNativePositiveRayMomentum R.energy R.direction+
      srNativePositiveRayMomentum R.energy (-R.direction))=
    ((mu,(0:SRSpace))+srNativePositiveRayMomentum R.energy (-R.direction)+
      srNativePositiveRayMomentum R.energy R.direction)
  receipt_relay_at_distinct_sites_geometry : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (distinct : S.position j ≠ S.position i) (emit delay energy : ℝ),
    0 < (relayAtSites S i j emit delay energy).length ∧
    ‖(relayAtSites S i j emit delay energy).direction‖=1 ∧
    relayY (relayAtSites S i j emit delay energy)=S.position j
  receipt_occupied_radar_readings : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (positive_i : 0 < mu0+S.internalEnergy i) (positive_j : 0 < mu0+S.internalEnergy j)
    (emit delay energy : ℝ),
    let R := relayAtSites S i j emit delay energy
    siteReading mu0 S j (relayArrival R).1-
      (siteReading mu0 S i (relayDeparture R).1+siteReading mu0 S i (relayReturn R).1-delay)/2=S.phase j-S.phase i ∧
    siteReading mu0 S j (relayRelease R).1-siteReading mu0 S j (relayArrival R).1=delay ∧
    (siteReading mu0 S i (relayReturn R).1-siteReading mu0 S i (relayDeparture R).1-delay)/2=R.length
  receipt_recorded_delay_arrival_departure : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (tm tp d arrival departure : ℝ)
    (midpoint : arrival=(tm+tp-d)/2) (delay : departure-arrival=d),
    arrival=(tm+tp-d)/2 ∧ departure=(tm+tp+d)/2
  receipt_phase_path_telescope : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {ι : Type} (phase : ι → ℝ) (i : ι) (tail : List ι),
    phasePath phase (i::tail)=phase (pathEnd i tail)-phase i
  receipt_phase_path_loop_zero : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {ι : Type} (phase : ι → ℝ) (i : ι) (tail : List ι)
    (closed : pathEnd i tail=i),
    phasePath phase (i::tail)=0
  receipt_every_nonzero_endpoint_standard_has_actual_radar_and_measuring_use : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint)
    (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (X Y : SRSpace) (distinct : Y ≠ X) (phaseX phaseY : ℝ)
    (Q : MeasuringQuery) (admitted : Q.frame ∈ srNativeFrameComparisons),
    ∃ d : NetworkData a s Omega 1, networkSound a s Omega 1 d ∧
      d.sites.position 0=X ∧ d.sites.position 1=Y ∧
      ∃ radar measurement, radarRead a s Omega 1 d 0 0=some radar ∧
        radar.length=‖Y-X‖ ∧ measuringRead a s Omega 1 d Q 0 1=some measurement
  receipt_old_licensed_consumer_has_actual_passive_source : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (r : LicensedNetworkReceiver a s Omega n) (i : Fin (n+1)),
    licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n (licensedNetworkPassive a s Omega n B admitted c r) i)=
      (⟨srPassiveClockUse a.mass B c (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).clock,
        (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).scalar,
        (licensedJointSRSource a s Omega (licensedNetworkToOld a s Omega n r i)).metric⟩ : JointOriginalSource a s Omega)
  receipt_positive_speed_beta_is_subluminal : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (c v : ℝ) (speed : 0 < c) (velocity : v^2 < c^2),
    (v/c)^2 < 1
  receipt_physical_rest_duration_is_actual_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (c t : ℝ) (speed : 0 < c) (forward : 0 ≤ t),
    physicalDuration c (t,0)=t
  receipt_actual_directional_clock_readings_in_physical_units : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 J : ℝ) (positive : 0 < mu0+J)
    (U : SREvent) (unit : IsFutureUnit U) (x : SRSpace) (phase c t u : ℝ) (speed : 0 < c),
    ((srNativeClockCoastFlow mu0 (c*u*U.1) (directionalClock mu0 J U x phase)).reading-
      (srNativeClockCoastFlow mu0 (c*t*U.1) (directionalClock mu0 J U x phase)).reading)/c=u-t
  receipt_occupied_radar_physical_units : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (positive_i : 0 < mu0+S.internalEnergy i) (positive_j : 0 < mu0+S.internalEnergy j)
    (emit delay energy c : ℝ) (speed : 0 < c),
    let R := relayAtSites S i j emit delay energy
    (siteReading mu0 S j (relayRelease R).1-siteReading mu0 S j (relayArrival R).1)/c=delay/c ∧
    c*((siteReading mu0 S i (relayReturn R).1-siteReading mu0 S i (relayDeparture R).1)/c-delay/c)/2=R.length ∧
    (siteReading mu0 S i (relayReturn R).1-siteReading mu0 S i (relayDeparture R).1)/c=(2*R.length+delay)/c
  receipt_actual_tick_dilation_in_physical_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (beta : ℝ) (subluminal : beta^2 < 1)
    (b : SREvent) (u v c : ℝ) (speed : 0 < c),
    ((frameEvent (measurementBoost beta subluminal) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) v)).1-
      (frameEvent (measurementBoost beta subluminal) b (srMarkedClockEvent mu0 (siteRecord mu0 S i) u)).1)/c=
    lorentzGamma beta*((siteReading mu0 S i v-siteReading mu0 S i u)/c)
  receipt_populated_network_every_declared_valid_request_is_executed : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phases : Fin (n+1) → ℝ) (lo hi : ℝ)
    (schedule : List (ExchangeRequest n)) (index : ℕ) (request : ExchangeRequest n)
    (registered : schedule[index]?=some request)
    (distinct : sites request.toSite ≠ sites request.fromSite) (energy : 0 < request.energy)
    (delay : 0 ≤ request.delay) (start : lo ≤ request.emit)
    (finish : request.emit+2*‖sites request.toSite-sites request.fromSite‖+request.delay ≤ hi),
    requestDomain a s Omega n (populatedNetworkData a s Omega n r H sites phases lo hi schedule) index request.delay
  receipt_populated_network_radar_success_is_inhabited : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega}),
    ∃ d : NetworkData a s Omega 1, networkSound a s Omega 1 d ∧
      ∃ answer : RadarAnswer, radarRead a s Omega 1 d 0 2=some answer ∧ answer.length=1
  receipt_actual_site_passive_slope : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {k : ℕ} (S : SiteData k) (i : Fin (k+1))
    (positive : 0 < mu0+S.internalEnergy i) (A : SRMatrixFrame),
    srPassiveClockSlope mu0 A (siteRecord mu0 S i).2.2=observerSlope A
  receipt_network_raw_use_is_actual_passive_rest_rebase : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (x : NetworkSource a s Omega n)
    (sound : networkSound a s Omega n x.data) (i : Fin (n+1)),
    (networkRawJoint a s Omega n x i).clock=srPassiveClockUse a.mass x.data.frame x.data.origin
      (srNativeClockUseRedescription a.mass (x.epoch i) (siteUse a.mass x.data.sites i x.data.lo x.data.hi))
  receipt_network_passive_source_is_same_actual_old_clock : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (B : SRMatrixFrame) (admitted : B ∈ srNativeFrameComparisons)
    (c : SREvent) (x : NetworkSource a s Omega n) (sound : networkSound a s Omega n x.data) (i : Fin (n+1)),
    (networkRawJoint a s Omega n (passiveNetwork a s Omega n B c x) i).clock=
      srPassiveClockUse a.mass B c (networkRawJoint a s Omega n x i).clock
  receipt_relay_compensator_full_legs_are_original_rays : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData) (unit : ‖R.direction‖=1),
    relayTurn R-relayCompensatorIncoming R ∈ srOriginalFutureRayIncrements ∧
    relayCompensatorOutgoing R-relayTurn R ∈ srOriginalFutureRayIncrements
  receipt_relay_whole_affine_domain_populated : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData),
    relayCovered univ R
  receipt_relay_whole_segments_transport : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (b : SREvent) (O : Set SREvent) (R : RelayData),
    relayCovered O R ↔ ∀ edge ∈ relaySegments R,
      segmentCovered (frameEvent A b '' O) (frameEvent A b edge.1) (frameEvent A b edge.2)
  receipt_protocol_time_slab_open : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (lo hi : ℝ),
    IsOpen (protocolTimeSlab lo hi)
  receipt_time_slab_full_segment : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (lo hi : ℝ) (p q : SREvent)
    (pin : p ∈ protocolTimeSlab lo hi) (qin : q ∈ protocolTimeSlab lo hi),
    segmentCovered (protocolTimeSlab lo hi) p q
  receipt_relay_proper_restricted_domain_populated : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (R : RelayData) (length : 0 < R.length)
    (delay : 0 ≤ R.delay),
    relayCovered (protocolTimeSlab (R.emit-2) ((relayReturn R).1+2)) R ∧
    protocolTimeSlab (R.emit-2) ((relayReturn R).1+2) ≠ univ
  receipt_synchronization_unique_on_actual_component : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {ι : Type} (edge : ι → ι → Prop)
    (phase other : ι → ℝ) (same_offsets : ∀ i j, edge i j → other j-other i=phase j-phase i)
    (i j : ι) (path : AdmittedPath edge i j),
    other j-phase j=other i-phase i
  receipt_all_pairs_synchronization_has_one_origin : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ {n : ℕ} (phase other : Fin (n+1) → ℝ)
    (same_offsets : ∀ i j, other j-other i=phase j-phase i),
    ∃ origin : ℝ, ∀ i, other i=phase i+origin
  receipt_restUnit_future : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), IsFutureUnit restUnit
  receipt_site_actual_event : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (t : ℝ),
    srMarkedClockEvent mu0 (siteRecord mu0 S i) t=(t,S.position i)
  receipt_site_actual_reading : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (t : ℝ),
    (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) t).2.reading=S.phase i+t
  receipt_site_use_actually_valid : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i : Fin (n+1))
    (positive : 0 < mu0+S.internalEnergy i) (lo hi : ℝ) (ordered : lo ≤ hi),
    srNativeClockUseValid mu0 (siteUse mu0 S i lo hi)
  receipt_framed_site_use_actually_valid : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) (base : 0 < mu0) {n : ℕ}
    (S : SiteData n) (i : Fin (n+1)) (positive : 0 < mu0+S.internalEnergy i)
    (lo hi : ℝ) (ordered : lo ≤ hi) (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (b : SREvent) (epoch : ℝ),
    srNativeClockUseValid mu0 (framedSiteUse mu0 S i lo hi A b epoch)
  receipt_site_phases_are_actual_offsets : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (mu0 : ℝ) {n : ℕ} (S : SiteData n) (i j : Fin (n+1))
    (positive_i : 0 < mu0+S.internalEnergy i) (positive_j : 0 < mu0+S.internalEnergy j) (t : ℝ),
    (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S j) t).2.reading-
      (srNativeCoastingMarkedRecord mu0 (siteRecord mu0 S i) t).2.reading=S.phase j-S.phase i
  receipt_rest_length_positive : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    0 < restLength w
  receipt_rest_length_square : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    (restLength w)^2=w.1^2-‖w.2‖^2
  receipt_normalized_tangent_is_future_unit : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    IsFutureUnit (normalizedTangent w)
  receipt_rest_length_times_normalized_tangent : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    restLength w • normalizedTangent w=w
  receipt_outbound_frame_mem : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    outboundFrame w future ∈ srNativeFrameComparisons
  receipt_outbound_frame_actual_interval : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    srMatrixFrameEventLinear (outboundFrame w future) (restLength w,0)=w
  receipt_actual_rest_presentation : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    restFrame w future ∈ srNativeFrameComparisons ∧
      srMatrixFrameEventLinear (restFrame w future) w=(restLength w,0)
  receipt_actual_successful_radar_has_proper_open_domain : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (r : LicensedScalarReceiver a s Omega (scalarBaseObject a))
    (H : {H : MetricSourceProbe Omega // H ∈ wickOriginalMetricNeighborhood Omega})
    (sites : Fin (n+1) → SRSpace) (phase : Fin (n+1) → ℝ) (i j : Fin (n+1))
    (distinct : sites j ≠ sites i) (emit delay energy : ℝ) (wait : 0 ≤ delay) (positive : 0 < energy),
    ∃ d : NetworkData a s Omega n, networkSound a s Omega n d ∧ IsOpen d.region ∧ d.region ≠ univ ∧
      ∃ answer : RadarAnswer, radarRead a s Omega n d 0 delay=some answer ∧
        answer.length=‖sites j-sites i‖
  receipt_rotated_boost_is_actually_admitted : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t),
    srRestCoordinateUnit Q*srUnitAxialBoost t r hyper ∈ srNativeFrameComparisons
  receipt_rotated_boost_actual_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (t r : ℝ) (hyper : t^2-r^2=1) (b z : SREvent),
    (frameEvent (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b z).1=
      (frameEvent (srUnitAxialBoost t r hyper) b z).1
  receipt_rotated_measuring_time_is_actual_selected_time : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X : SRSpace),
    measuringSiteTime ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ X=selectedRestTime t r b T X
  receipt_general_measuring_separation_is_actual_source_form : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) (b : SREvent) (T : ℝ) (X Y : SRSpace),
    ‖(measuredEndpoint A b T Y).2-(measuredEndpoint A b T X).2‖^2=
      ‖Y-X‖^2-(selectedSiteTime A b T Y-selectedSiteTime A b T X)^2
  receipt_rotated_actual_selected_length_squared : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X Y : SRSpace),
    ‖(measuredEndpoint (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b T Y).2-
      (measuredEndpoint (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b T X).2‖^2=
      (Y 0-X 0)^2/t^2+(Y 1-X 1)^2+(Y 2-X 2)^2
  receipt_successful_rotated_ruler_is_actual_measurement : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint)
    (n : ℕ) (d : NetworkData a s Omega n) (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (i j : Fin (n+1))
    (domain : measuringDomain a s Omega n d ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ i j),
    ∃ answer : MeasuringAnswer,
      measuringRead a s Omega n d ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ i j=some answer ∧
      answer.length^2=(d.sites.position j 0-d.sites.position i 0)^2/t^2+
        (d.sites.position j 1-d.sites.position i 1)^2+(d.sites.position j 2-d.sites.position i 2)^2
  receipt_actual_source_form_smul : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (t : ℝ) (w : SREvent),
    srOriginalOrderQuadratic (t • w)=t^2*srOriginalOrderQuadratic w
  receipt_actual_source_form_zero : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), srOriginalOrderQuadratic (0:SREvent)=0
  receipt_native_frame_source_quadratic : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent),
    srOriginalOrderQuadratic (srMatrixFrameEventLinear A w)=srOriginalOrderQuadratic w
  receipt_future_timelike_strict_cone : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (w : SREvent) (future : IsFutureTimelike w),
    ‖w.2‖ < w.1
  receipt_native_frame_preserves_future_timelike : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent) (future : IsFutureTimelike w),
    IsFutureTimelike (srMatrixFrameEventLinear A w)
  receipt_native_frame_future_timelike_iff : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent),
    IsFutureTimelike w ↔ IsFutureTimelike (srMatrixFrameEventLinear A w)
  receipt_future_unit_positive_scale : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (U : SREvent) (unit : IsFutureUnit U) (t : ℝ) (positive : 0 < t),
    IsFutureTimelike (t • U)
  receipt_future_unit_scaled_rest_length : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (U : SREvent) (unit : IsFutureUnit U) (t : ℝ) (positive : 0 ≤ t),
    restLength (t • U)=t
  receipt_native_rest_time_is_actual_length : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) (w : SREvent) (future : IsFutureTimelike w)
    (atRest : (srMatrixFrameEventLinear A w).2=0),
    srMatrixFrameEventLinear A w=(restLength w,0)
  receipt_rest_length_native_frame : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent),
    restLength (srMatrixFrameEventLinear A w)=restLength w
  receipt_normalized_tangent_native_frame : ∀ (Omega : Opens CoordinatePoint) (n : ℕ), ∀ (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (w : SREvent),
    normalizedTangent (srMatrixFrameEventLinear A w)=
      srMatrixFrameEventLinear A (normalizedTangent w)

theorem kernel_faithful_operational_sr (a : Parameters) (s kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    KernelFaithfulOperationalSR a s kappa Lambda where
  retained_stage3 := RecoveryComparison.kernel_faithful_recovery_comparison a s kappa Lambda coupling
  retained_native_sr := kernel_faithful_native_sr_canonical_licensing_eh_scalar a s
  receipt_recorded_delay_radar_derived_from_actual_null_legs := fun Omega n => @recorded_delay_radar_derived_from_actual_null_legs
  receipt_every_successful_radar_answer_is_actual := fun Omega n => @every_successful_radar_answer_is_actual a s Omega n
  receipt_occupied_radar_path_sum_is_actual_phase_difference := fun Omega n => @occupied_radar_path_sum_is_actual_phase_difference a s Omega n
  receipt_every_occupied_radar_loop_sums_to_zero := fun Omega n => @every_occupied_radar_loop_sums_to_zero a s Omega n
  receipt_measured_ruler_answer_has_actual_simultaneous_events := fun Omega n => @measured_ruler_answer_has_actual_simultaneous_events a s Omega n
  receipt_actual_affine_identity := fun Omega n => @actual_affine_identity
  receipt_actual_affine_open_domain_transport := fun Omega n => @actual_affine_open_domain_transport
  receipt_actual_affine_inverse_is_the_inverse_frame := fun Omega n => @actual_affine_inverse_is_the_inverse_frame
  receipt_frame_inverse_left := fun Omega n => @frame_inverse_left
  receipt_frame_inverse_right := fun Omega n => @frame_inverse_right
  receipt_frame_event_injective := fun Omega n => @frame_event_injective
  receipt_frame_event_composition := fun Omega n => @frame_event_composition
  receipt_frame_event_difference := fun Omega n => @frame_event_difference
  receipt_frame_preserves_actual_source_form := fun Omega n => @frame_preserves_actual_source_form
  receipt_frame_barycentric := fun Omega n => @frame_barycentric
  receipt_actual_segment_domain_transport := fun Omega n => @actual_segment_domain_transport
  receipt_whole_affine_segments_populated := fun Omega n => @whole_affine_segments_populated
  receipt_axis_boost_actually_admitted := fun Omega n => @axis_boost_actually_admitted
  receipt_actual_inverse_rotation_event := fun Omega n => @actual_inverse_rotation_event
  receipt_actual_axis_boost_time := fun Omega n => @actual_axis_boost_time
  receipt_actual_axis_selected_rest_time := fun Omega n => @actual_axis_selected_rest_time
  receipt_arbitrary_axis_actual_measured_length := fun Omega n => @arbitrary_axis_actual_measured_length
  receipt_arbitrary_axis_actual_selected_time_gap := fun Omega n => @arbitrary_axis_actual_selected_time_gap
  receipt_auxiliary_actual_clock_full_marked_state_passive := fun Omega n => @auxiliary_actual_clock_full_marked_state_passive a s Omega n
  receipt_native_frame_preserves_unit := fun Omega n => @native_frame_preserves_unit
  receipt_directional_clock_marked_event := fun Omega n => @directional_clock_marked_event
  receipt_directional_clock_actual_passive_state := fun Omega n => @directional_clock_actual_passive_state
  receipt_directional_clock_actual_passive_use := fun Omega n => @directional_clock_actual_passive_use
  receipt_directional_clock_actual_frame_readout := fun Omega n => @directional_clock_actual_frame_readout
  receipt_directional_joint_actual_valid := fun Omega n => @directional_joint_actual_valid a s Omega
  receipt_licensed_directional_actual_source := fun Omega n => @licensed_directional_actual_source a s Omega
  receipt_licensed_directional_original_preparations := fun Omega n => @licensed_directional_original_preparations a s Omega
  receipt_directional_actual_canonical_license := fun Omega n => @directional_actual_canonical_license a s Omega
  receipt_directional_actual_eh_operand := fun Omega n => @directional_actual_eh_operand a s Omega
  receipt_directional_actual_registered_reference := fun Omega n => @directional_actual_registered_reference a s Omega
  receipt_actual_occupied_path_is_connected := fun Omega n => @actual_occupied_path_is_connected a s Omega n
  receipt_actual_undirected_component_synchronization_unique := fun Omega n => @actual_undirected_component_synchronization_unique a s Omega n
  receipt_actual_undirected_component_has_one_common_origin := fun Omega n => @actual_undirected_component_has_one_common_origin a s Omega n
  receipt_directional_clock_actual_mass := fun Omega n => @directional_clock_actual_mass
  receipt_directional_clock_actual_hamiltonian := fun Omega n => @directional_clock_actual_hamiltonian
  receipt_directional_clock_actual_proper_tangent := fun Omega n => @directional_clock_actual_proper_tangent
  receipt_directional_clock_actual_rate := fun Omega n => @directional_clock_actual_rate
  receipt_directional_clock_actual_event := fun Omega n => @directional_clock_actual_event
  receipt_directional_clock_actual_reading := fun Omega n => @directional_clock_actual_reading
  receipt_directional_clock_use_actual_interval := fun Omega n => @directional_clock_use_actual_interval
  receipt_directional_clock_use_actually_valid := fun Omega n => @directional_clock_use_actually_valid
  receipt_directional_clock_complete_marked_record := fun Omega n => @directional_clock_complete_marked_record
  receipt_all_pairs_request_actually_registered := fun Omega n => @all_pairs_request_actually_registered n
  receipt_finite_all_pairs_network_is_actually_occupied := fun Omega n => @finite_all_pairs_network_is_actually_occupied a s Omega n
  receipt_synchronization_from_actual_successful_graph := fun Omega n => @synchronization_from_actual_successful_graph a s Omega n
  receipt_actual_component_synchronization_unique := fun Omega n => @actual_component_synchronization_unique a s Omega n
  receipt_actual_radar_reversal_from_successful_records := fun Omega n => @actual_radar_reversal_from_successful_records a s Omega n
  receipt_axial_boost_rest_vector := fun Omega n => @axial_boost_rest_vector
  receipt_proper_spatial_rotation_actually_supplied := fun Omega n => @proper_spatial_rotation_actually_supplied
  receipt_actual_native_future_unit_frame_supply := fun Omega n => @actual_native_future_unit_frame_supply
  receipt_supplied_unit_frame_mem := fun Omega n => @supplied_unit_frame_mem
  receipt_supplied_unit_frame_rest := fun Omega n => @supplied_unit_frame_rest
  receipt_auxiliary_endpoint_original_read_and_failure_transport := fun Omega n => @auxiliary_endpoint_original_read_and_failure_transport a s Omega n
  receipt_unregistered_auxiliary_failure_retained := fun Omega n => @unregistered_auxiliary_failure_retained a s Omega n
  receipt_original_coordinate_ruler_same_question_transport := fun Omega n => @original_coordinate_ruler_same_question_transport a s Omega n
  receipt_site_event_and_reading_same_question_transport := fun Omega n => @site_event_and_reading_same_question_transport a s Omega n
  receipt_full_licensed_operation_physical_refinement_square := fun Omega n => @full_licensed_operation_physical_refinement_square a s Omega n
  receipt_rest_unit_is_future_unit := fun Omega n => @rest_unit_is_future_unit
  receipt_ideal_duration_zero := fun Omega n => @ideal_duration_zero
  receipt_ideal_rest_response_derived := fun Omega n => @ideal_rest_response_derived
  receipt_ideal_inertial_response_classification := fun Omega n => @ideal_inertial_response_classification
  receipt_ideal_inertial_response_unique := fun Omega n => @ideal_inertial_response_unique
  receipt_ideal_response_read_domain := fun Omega n => @ideal_response_read_domain
  receipt_gamma_positive_and_hyperbolic := fun Omega n => @gamma_positive_and_hyperbolic
  receipt_measurement_boost_actually_supplied := fun Omega n => @measurement_boost_actually_supplied
  receipt_axial_boost_spatial_components := fun Omega n => @axial_boost_spatial_components
  receipt_endpoint_selection_is_simultaneous_and_unique := fun Omega n => @endpoint_selection_is_simultaneous_and_unique
  receipt_actual_selected_endpoint_separation := fun Omega n => @actual_selected_endpoint_separation
  receipt_actual_selected_length_squared := fun Omega n => @actual_selected_length_squared
  receipt_measurement_selected_rest_time_gap := fun Omega n => @measurement_selected_rest_time_gap
  receipt_fixed_event_pair_passive_simultaneity := fun Omega n => @fixed_event_pair_passive_simultaneity
  receipt_same_bearer_ticks_actual_dilation := fun Omega n => @same_bearer_ticks_actual_dilation
  receipt_actual_orientation_preserves_measured_length := fun Omega n => @actual_orientation_preserves_measured_length
  receipt_physical_time_adapter_inverse := fun Omega n => @physical_time_adapter_inverse
  receipt_licensed_network_operation_actual_source_square := fun Omega n => @licensed_network_operation_actual_source_square a s Omega n
  receipt_licensed_network_operation_actual_readout_square := fun Omega n => @licensed_network_operation_actual_readout_square a s Omega n
  receipt_licensed_network_operation_domain_is_exact := fun Omega n => @licensed_network_operation_domain_is_exact a s Omega n
  receipt_licensed_network_full_finite_first_failure_square := fun Omega n => @licensed_network_full_finite_first_failure_square a s Omega n
  receipt_licensed_network_passive_source_square := fun Omega n => @licensed_network_passive_source_square a s Omega n
  receipt_licensed_network_passive_full_first_failure := fun Omega n => @licensed_network_passive_full_first_failure a s Omega n
  receipt_selected_network_event_and_reading_are_actual := fun Omega n => @selected_network_event_and_reading_are_actual a s Omega n
  receipt_actual_reference_advance_selected_event_and_reading := fun Omega n => @actual_reference_advance_selected_event_and_reading a s Omega n
  receipt_local_rest_response_zero := fun Omega n => @local_rest_response_zero
  receipt_local_rest_response_monotone := fun Omega n => @local_rest_response_monotone
  receipt_local_rest_response_nsmul := fun Omega n => @local_rest_response_nsmul
  receipt_calibrated_rest_grid_error := fun Omega n => @calibrated_rest_grid_error
  receipt_calibrated_local_rest_response_unique := fun Omega n => @calibrated_local_rest_response_unique
  receipt_passive_full_marked_state_composition := fun Omega n => @passive_full_marked_state_composition
  receipt_passive_full_marked_state_is_actual := fun Omega n => @passive_full_marked_state_is_actual
  receipt_retained_measuring_answer_is_same_actual_clock := fun Omega n => @retained_measuring_answer_is_same_actual_clock a s Omega n
  receipt_original_coordinate_ruler_is_retained_query_specialization := fun Omega n => @original_coordinate_ruler_is_retained_query_specialization a s Omega n
  receipt_licensed_measuring_read_same_question_passive := fun Omega n => @licensed_measuring_read_same_question_passive a s Omega n
  receipt_registered_protocol_ledger_is_exactly_retained := fun Omega n => @registered_protocol_ledger_is_exactly_retained a s Omega n
  receipt_observer_slope_actually_positive := fun Omega n => @observer_slope_actually_positive
  receipt_actual_site_event_affine_time := fun Omega n => @actual_site_event_affine_time
  receipt_measuring_frame_selected_events_actual_and_unique := fun Omega n => @measuring_frame_selected_events_actual_and_unique
  receipt_general_selection_is_actual_axial_selection := fun Omega n => @general_selection_is_actual_axial_selection
  receipt_same_measuring_hyperplane_is_actually_transported := fun Omega n => @same_measuring_hyperplane_is_actually_transported
  receipt_measured_endpoint_lies_on_retained_hyperplane := fun Omega n => @measured_endpoint_lies_on_retained_hyperplane
  receipt_presented_selected_event_transport := fun Omega n => @presented_selected_event_transport
  receipt_native_duration_zero := fun Omega n => @native_duration_zero
  receipt_native_duration_is_actual_metric_length := fun Omega n => @native_duration_is_actual_metric_length
  receipt_native_duration_unit_scale := fun Omega n => @native_duration_unit_scale
  receipt_native_certified_frame := fun Omega n => @native_certified_frame
  receipt_native_duration_same_event_frame := fun Omega n => @native_duration_same_event_frame
  receipt_native_duration_has_actual_original_use := fun Omega n => @native_duration_has_actual_original_use
  receipt_native_interval_use_is_same_passively_transported_clock := fun Omega n => @native_interval_use_is_same_passively_transported_clock
  receipt_network_data_operation_retains_actual_records := fun Omega n => @network_data_operation_retains_actual_records a s Omega n
  receipt_network_raw_record_is_same_marked_history := fun Omega n => @network_raw_record_is_same_marked_history a s Omega n
  receipt_network_all_successful_operations_retain_underlying_histories := fun Omega n => @network_all_successful_operations_retain_underlying_histories a s Omega n
  receipt_site_window_extension_is_actual_old_extension := fun Omega n => @site_window_extension_is_actual_old_extension
  receipt_network_window_extension_has_actual_coordinate_slope := fun Omega n => @network_window_extension_has_actual_coordinate_slope a s Omega n
  receipt_network_nonnegative_reference_advance_is_actual := fun Omega n => @network_nonnegative_reference_advance_is_actual a s Omega n
  receipt_network_continuation_selection_exit_is_retained := fun Omega n => @network_continuation_selection_exit_is_retained a s Omega n
  receipt_network_receiver_operation_square := fun Omega n => @network_receiver_operation_square a s Omega n
  receipt_network_finite_first_failure_square := fun Omega n => @network_finite_first_failure_square a s Omega n
  receipt_licensed_network_same_metric_operand := fun Omega n => @licensed_network_same_metric_operand a s Omega n
  receipt_licensed_network_complete_registered_reference := fun Omega n => @licensed_network_complete_registered_reference a s Omega n
  receipt_network_rebase_preserves_complete_profile := fun Omega n => @network_rebase_preserves_complete_profile a s Omega n
  receipt_network_data_operation_preserves_sound := fun Omega n => @network_data_operation_preserves_sound a s Omega n
  receipt_network_operation_preserves_actual_sound_region := fun Omega n => @network_operation_preserves_actual_sound_region a s Omega n
  receipt_network_actual_source_passes_local_tests := fun Omega n => @network_actual_source_passes_local_tests a s Omega n
  receipt_network_actual_sound_region_postfixed := fun Omega n => @network_actual_sound_region_postfixed a s Omega n
  receipt_actual_network_source_has_kernel_faithful_license := fun Omega n => @actual_network_source_has_kernel_faithful_license a s Omega n
  receipt_licensed_network_has_actual_sound_source := fun Omega n => @licensed_network_has_actual_sound_source a s Omega n
  receipt_licensed_network_old_actual_raw_source_square := fun Omega n => @licensed_network_old_actual_raw_source_square a s Omega n
  receipt_licensed_network_old_preparations_square := fun Omega n => @licensed_network_old_preparations_square a s Omega n
  receipt_passive_network_actually_sound := fun Omega n => @passive_network_actually_sound a s Omega n
  receipt_inverse_chart_after_actual_presentation := fun Omega n => @inverse_chart_after_actual_presentation
  receipt_inverse_chart_domain_image := fun Omega n => @inverse_chart_domain_image
  receipt_passive_network_request_domain := fun Omega n => @passive_network_request_domain a s Omega n
  receipt_passive_network_measuring_domain := fun Omega n => @passive_network_measuring_domain a s Omega n
  receipt_actual_measuring_answer_same_question_transport := fun Omega n => @actual_measuring_answer_same_question_transport a s Omega n
  receipt_measuring_read_same_question_transport_and_failure := fun Omega n => @measuring_read_same_question_transport_and_failure a s Omega n
  receipt_network_partial_operation_passive_square := fun Omega n => @network_partial_operation_passive_square a s Omega n
  receipt_network_operation_retains_presentation := fun Omega n => @network_operation_retains_presentation a s Omega n
  receipt_passive_program_parameter_stable := fun Omega n => @passive_program_parameter_stable a s Omega n
  receipt_passive_network_finite_first_failure := fun Omega n => @passive_network_finite_first_failure a s Omega n
  receipt_populated_network_actual_sound := fun Omega n => @populated_network_actual_sound a s Omega n
  receipt_inhabited_network_covers_every_old_preparation := fun Omega n => @inhabited_network_covers_every_old_preparation a s Omega n
  receipt_network_base_joint_actually_valid := fun Omega n => @network_base_joint_actually_valid a s Omega n
  receipt_network_raw_joint_actually_valid := fun Omega n => @network_raw_joint_actually_valid a s Omega n
  receipt_network_licensed_site_retains_actual_raw_source := fun Omega n => @network_licensed_site_retains_actual_raw_source a s Omega n
  receipt_radar_read_exact_domain := fun Omega n => @radar_read_exact_domain a s Omega n
  receipt_occupied_network_radar_answer := fun Omega n => @occupied_network_radar_answer a s Omega n
  receipt_relay_extra_endpoint_is_actual_positive_clock := fun Omega n => @relay_extra_endpoint_is_actual_positive_clock a s Omega n
  receipt_network_operation_actual_data_square := fun Omega n => @network_operation_actual_data_square a s Omega n
  receipt_network_complete_profile_factors_physical_data := fun Omega n => @network_complete_profile_factors_physical_data a s Omega n
  receipt_network_actual_raw_old_profile_square := fun Omega n => @network_actual_raw_old_profile_square a s Omega n
  receipt_network_old_physical_square := fun Omega n => @network_old_physical_square a s Omega n
  receipt_network_all_registered_operations_have_exact_descent := fun Omega n => @network_all_registered_operations_have_exact_descent a s Omega n
  receipt_network_failed_radar_attempt_is_retained := fun Omega n => @network_failed_radar_attempt_is_retained a s Omega n
  receipt_raw_network_clock_actual_same_event := fun Omega n => @raw_network_clock_actual_same_event a s Omega n
  receipt_raw_network_clock_actual_same_reading := fun Omega n => @raw_network_clock_actual_same_reading a s Omega n
  receipt_measured_network_endpoints_are_actual_same_clocks := fun Omega n => @measured_network_endpoints_are_actual_same_clocks a s Omega n
  receipt_relay_extra_endpoint_actual_passive_event_and_reading := fun Omega n => @relay_extra_endpoint_actual_passive_event_and_reading a s Omega n
  receipt_actual_radar_answer_passive := fun Omega n => @actual_radar_answer_passive a s Omega n
  receipt_actual_radar_read_and_failure_passive := fun Omega n => @actual_radar_read_and_failure_passive a s Omega n
  receipt_actual_signal_ledger_events_momenta_identities_passive := fun Omega n => @actual_signal_ledger_events_momenta_identities_passive a s Omega n
  receipt_signal_read_and_failure_passive := fun Omega n => @signal_read_and_failure_passive a s Omega n
  receipt_protocol_and_reference_are_retained_under_passive := fun Omega n => @protocol_and_reference_are_retained_under_passive a s Omega n
  receipt_actual_native_ideal_class_is_occupied := fun Omega n => @actual_native_ideal_class_is_occupied
  receipt_relay_main_crossing_records := fun Omega n => @relay_main_crossing_records
  receipt_relay_compensator_shared_vertex := fun Omega n => @relay_compensator_shared_vertex
  receipt_relay_full_legs_are_actual_original_rays := fun Omega n => @relay_full_legs_are_actual_original_rays
  receipt_relay_positive_energy_and_balanced_vertex := fun Omega n => @relay_positive_energy_and_balanced_vertex
  receipt_relay_at_distinct_sites_geometry := fun Omega n => @relay_at_distinct_sites_geometry
  receipt_occupied_radar_readings := fun Omega n => @occupied_radar_readings
  receipt_recorded_delay_arrival_departure := fun Omega n => @recorded_delay_arrival_departure
  receipt_phase_path_telescope := fun Omega n => @phase_path_telescope
  receipt_phase_path_loop_zero := fun Omega n => @phase_path_loop_zero
  receipt_every_nonzero_endpoint_standard_has_actual_radar_and_measuring_use := fun Omega n => @every_nonzero_endpoint_standard_has_actual_radar_and_measuring_use
  receipt_old_licensed_consumer_has_actual_passive_source := fun Omega n => @old_licensed_consumer_has_actual_passive_source a s Omega n
  receipt_positive_speed_beta_is_subluminal := fun Omega n => @positive_speed_beta_is_subluminal
  receipt_physical_rest_duration_is_actual_time := fun Omega n => @physical_rest_duration_is_actual_time
  receipt_actual_directional_clock_readings_in_physical_units := fun Omega n => @actual_directional_clock_readings_in_physical_units
  receipt_occupied_radar_physical_units := fun Omega n => @occupied_radar_physical_units
  receipt_actual_tick_dilation_in_physical_time := fun Omega n => @actual_tick_dilation_in_physical_time
  receipt_populated_network_every_declared_valid_request_is_executed := fun Omega n => @populated_network_every_declared_valid_request_is_executed a s Omega n
  receipt_populated_network_radar_success_is_inhabited := fun Omega n => @populated_network_radar_success_is_inhabited a s Omega
  receipt_actual_site_passive_slope := fun Omega n => @actual_site_passive_slope
  receipt_network_raw_use_is_actual_passive_rest_rebase := fun Omega n => @network_raw_use_is_actual_passive_rest_rebase a s Omega n
  receipt_network_passive_source_is_same_actual_old_clock := fun Omega n => @network_passive_source_is_same_actual_old_clock a s Omega n
  receipt_relay_compensator_full_legs_are_original_rays := fun Omega n => @relay_compensator_full_legs_are_original_rays
  receipt_relay_whole_affine_domain_populated := fun Omega n => @relay_whole_affine_domain_populated
  receipt_relay_whole_segments_transport := fun Omega n => @relay_whole_segments_transport
  receipt_protocol_time_slab_open := fun Omega n => @protocol_time_slab_open
  receipt_time_slab_full_segment := fun Omega n => @time_slab_full_segment
  receipt_relay_proper_restricted_domain_populated := fun Omega n => @relay_proper_restricted_domain_populated
  receipt_synchronization_unique_on_actual_component := fun Omega n => @synchronization_unique_on_actual_component
  receipt_all_pairs_synchronization_has_one_origin := fun Omega n => @all_pairs_synchronization_has_one_origin
  receipt_restUnit_future := fun Omega n => @restUnit_future
  receipt_site_actual_event := fun Omega n => @site_actual_event
  receipt_site_actual_reading := fun Omega n => @site_actual_reading
  receipt_site_use_actually_valid := fun Omega n => @site_use_actually_valid
  receipt_framed_site_use_actually_valid := fun Omega n => @framed_site_use_actually_valid
  receipt_site_phases_are_actual_offsets := fun Omega n => @site_phases_are_actual_offsets
  receipt_rest_length_positive := fun Omega n => @rest_length_positive
  receipt_rest_length_square := fun Omega n => @rest_length_square
  receipt_normalized_tangent_is_future_unit := fun Omega n => @normalized_tangent_is_future_unit
  receipt_rest_length_times_normalized_tangent := fun Omega n => @rest_length_times_normalized_tangent
  receipt_outbound_frame_mem := fun Omega n => @outbound_frame_mem
  receipt_outbound_frame_actual_interval := fun Omega n => @outbound_frame_actual_interval
  receipt_actual_rest_presentation := fun Omega n => @actual_rest_presentation
  receipt_actual_successful_radar_has_proper_open_domain := fun Omega n => @actual_successful_radar_has_proper_open_domain a s Omega n
  receipt_rotated_boost_is_actually_admitted := fun Omega n => @rotated_boost_is_actually_admitted
  receipt_rotated_boost_actual_time := fun Omega n => @rotated_boost_actual_time
  receipt_rotated_measuring_time_is_actual_selected_time := fun Omega n => @rotated_measuring_time_is_actual_selected_time
  receipt_general_measuring_separation_is_actual_source_form := fun Omega n => @general_measuring_separation_is_actual_source_form
  receipt_rotated_actual_selected_length_squared := fun Omega n => @rotated_actual_selected_length_squared
  receipt_successful_rotated_ruler_is_actual_measurement := fun Omega n => @successful_rotated_ruler_is_actual_measurement
  receipt_actual_source_form_smul := fun Omega n => @actual_source_form_smul
  receipt_actual_source_form_zero := fun Omega n => @actual_source_form_zero
  receipt_native_frame_source_quadratic := fun Omega n => @native_frame_source_quadratic
  receipt_future_timelike_strict_cone := fun Omega n => @future_timelike_strict_cone
  receipt_native_frame_preserves_future_timelike := fun Omega n => @native_frame_preserves_future_timelike
  receipt_native_frame_future_timelike_iff := fun Omega n => @native_frame_future_timelike_iff
  receipt_future_unit_positive_scale := fun Omega n => @future_unit_positive_scale
  receipt_future_unit_scaled_rest_length := fun Omega n => @future_unit_scaled_rest_length
  receipt_native_rest_time_is_actual_length := fun Omega n => @native_rest_time_is_actual_length
  receipt_rest_length_native_frame := fun Omega n => @rest_length_native_frame
  receipt_normalized_tangent_native_frame := fun Omega n => @normalized_tangent_native_frame
end AASCKleinGordon.OperationalSR
