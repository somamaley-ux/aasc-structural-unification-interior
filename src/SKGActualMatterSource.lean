import SKGMetricRayProtocol
import SKGScalarStressBalance

/-! The source is constructed from the actual inherited matter-action ray
readout. It is not the geometric EH response and is not supplied as a field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def sameActionScalarMetricLF (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) : MetricSourceProbe (sourceDomain a) →L[ℝ] ℝ :=
  nativeScalarClockMetricLF (sourceMetric a) u (massWaveNumber a ^ 2)
    (source_metric_continuous a) regular (fun p _ => source_metric_nondegenerate a p)

def sameActionScalarSource (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) : SymmetricSourceComponents (sourceDomain a) :=
  representedMetricSource (sameActionScalarMetricLF a u regular)

theorem same_action_scalar_metric_derivative (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a) :
    HasDerivAt (scalarMetricRayAction a u protocol)
      (sameActionScalarMetricLF a u regular protocol.test) 0 :=
  native_scalar_clock_action_derivative_constructed (sourceMetric a) (source_metric_symmetric a)
    u (massWaveNumber a ^ 2) (source_metric_continuous a) regular
      (fun p _ => source_metric_nondegenerate a p) protocol.test

theorem same_action_ray_output_is_constructed_response (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a) :
    scalarMetricRayOutput a u protocol = sameActionScalarMetricLF a u regular protocol.test :=
  (same_action_scalar_metric_derivative a u regular protocol).deriv

theorem same_action_scalar_response_graph (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (h : MetricSourceProbe (sourceDomain a)) (y : ℝ) :
    sameActionScalarMetricLF a u regular h = y ↔
      ∃ protocol : ScalarMetricRayProtocol a,
        scalarMetricRayIncidence a h protocol ∧ scalarMetricRayOutput a u protocol = y := by
  constructor
  · intro equal
    refine ⟨⟨h⟩, rfl, ?_⟩
    rw [same_action_ray_output_is_constructed_response a u regular]
    exact equal
  · rintro ⟨protocol, incidence, output⟩
    rw [same_action_ray_output_is_constructed_response a u regular] at output
    change protocol.test = h at incidence
    simpa only [incidence] using output

theorem same_action_scalar_source_three_reader_square (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a) :
    (1 / 2 : ℝ) * metricSourcePairing (sameActionScalarSource a u regular) protocol.test =
      sameActionScalarMetricLF a u regular protocol.test ∧
    sameActionScalarMetricLF a u regular protocol.test = scalarMetricRayOutput a u protocol := by
  constructor
  · exact constructed_metric_source_represents _ _
  · exact (same_action_ray_output_is_constructed_response a u regular protocol).symm

theorem same_action_scalar_actual_source_unique (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) :
    ∃! T : SymmetricSourceComponents (sourceDomain a),
      ∀ protocol : ScalarMetricRayProtocol a,
        (1 / 2 : ℝ) * metricSourcePairing T protocol.test = scalarMetricRayOutput a u protocol := by
  refine ⟨sameActionScalarSource a u regular, ?_, ?_⟩
  · intro protocol
    exact (same_action_scalar_source_three_reader_square a u regular protocol).1.trans
      (same_action_scalar_source_three_reader_square a u regular protocol).2
  · intro T represents
    apply constructed_metric_source_unique (sameActionScalarMetricLF a u regular) T
    intro h
    exact (represents ⟨h⟩).trans (same_action_ray_output_is_constructed_response a u regular ⟨h⟩)

theorem scalar_clock_coefficient_is_raised_density_of_negative (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (u : CoordinatePoint → ℝ) (mu2 : ℝ)
    (p : CoordinatePoint) (negative : (g p).det < 0) (i : Fin 10) :
    nativeClockSourceCoefficient g (nativeScalarClockGradient u) u mu2 i p =
      sourceDensityCoordinates (raisedSourceTensorDensity g (scalarFieldStress g u mu2)) i p := by
  have hG : (g p).transpose = g p := by ext a b; exact symmetric p b a
  have hB : (g p)⁻¹.transpose = (g p)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hG]
  have hT : nativeRealClockStress (g p) (nativeScalarClockGradient u p) (u p) mu2 =
      scalarFieldStress g u mu2 p := native_real_clock_stress_is_actual_scalar_stress g u p mu2
  unfold nativeClockSourceCoefficient sourceDensityCoordinates raisedSourceTensorDensity
  rw [hT]
  have hdecode : tensorDecode ((g p)⁻¹ * scalarFieldStress g u mu2 p * (g p)⁻¹) i =
      ((g p)⁻¹ * scalarFieldStress g u mu2 p * (g p)⁻¹)
        (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 := by
    fin_cases i <;> rfl
  rw [hdecode, native_raise_source_matrix_identity _ _ hB]
  simp only [nativeRealClockVolume, coordinateVolumeDensity, abs_of_neg negative]

theorem same_action_source_represents_actual_stress (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
    sameActionScalarSource a u regular i psi =
      ∫ p, sourceDensityCoordinates
        (raisedSourceTensorDensity (sourceMetric a) (scalarFieldStress (sourceMetric a) u (massWaveNumber a ^ 2))) i p * psi p := by
  unfold sameActionScalarSource sameActionScalarMetricLF nativeScalarClockMetricLF
  rw [native_clock_constructed_source_integral_components]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    change nativeClockSourceCoefficient (sourceMetric a) (nativeScalarClockGradient u) u
      (massWaveNumber a ^ 2) i p * psi p =
        sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a)
          (scalarFieldStress (sourceMetric a) u (massWaveNumber a ^ 2))) i p * psi p
    rw [scalar_clock_coefficient_is_raised_density_of_negative (sourceMetric a)
      (source_metric_symmetric a) u _ p (source_metric_determinant_negative a p) i])

theorem same_action_response_additive (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (h k : MetricSourceProbe (sourceDomain a)) :
    scalarMetricRayOutput a u ⟨h + k⟩ =
      scalarMetricRayOutput a u ⟨h⟩ + scalarMetricRayOutput a u ⟨k⟩ := by
  simp only [same_action_ray_output_is_constructed_response a u regular]
  exact (sameActionScalarMetricLF a u regular).map_add h k

theorem same_action_response_homogeneous (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (r : ℝ) (h : MetricSourceProbe (sourceDomain a)) :
    scalarMetricRayOutput a u ⟨r • h⟩ = r * scalarMetricRayOutput a u ⟨h⟩ := by
  simp only [same_action_ray_output_is_constructed_response a u regular]
  exact (sameActionScalarMetricLF a u regular).map_smul r h

theorem same_action_response_lf_continuous (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) :
    Continuous (fun h : MetricSourceProbe (sourceDomain a) => scalarMetricRayOutput a u ⟨h⟩) := by
  simpa only [same_action_ray_output_is_constructed_response a u regular] using
    (sameActionScalarMetricLF a u regular).continuous

end AASCKleinGordon.SameActionSource
