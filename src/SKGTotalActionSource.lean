import SKGSourceOccupation
import OriginalEHGeometricTensor

/-! Same actual metric ray in both actions. The total response is derived
by differentiating their sum. Metric stationarity remains a hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def sameEHMetricLF (a : Parameters) (kappa Lambda : ℝ) (coupling : kappa ≠ 0) :
    MetricSourceProbe (sourceDomain a) →L[ℝ] ℝ :=
  originalEHFirstVariation kappa Lambda coupling (sourceMetric a) (source_metric_symmetric a)
    (source_metric_smooth a) (fun p _ => source_metric_determinant_negative a p)

def sameTotalMetricLF (a : Parameters) (kappa Lambda : ℝ) (coupling : kappa ≠ 0)
    (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) :
    MetricSourceProbe (sourceDomain a) →L[ℝ] ℝ :=
  sameEHMetricLF a kappa Lambda coupling + sameActionScalarMetricLF a u regular

def sameTotalRayAction (a : Parameters) (kappa Lambda : ℝ) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) (t : ℝ) : ℝ :=
  originalEHRelativeAction kappa Lambda (sourceMetric a) (t • protocol.test) +
    scalarMetricRayAction a u protocol t

def SameTotalMetricStationary (a : Parameters) (kappa Lambda : ℝ)
    (u : CoordinatePoint → ℝ) : Prop :=
  ∀ protocol : ScalarMetricRayProtocol a, deriv (sameTotalRayAction a kappa Lambda u protocol) 0 = 0

def totalActualDensity (a : Parameters) (kappa Lambda : ℝ) (u : CoordinatePoint → ℝ)
    (i : Fin 10) (p : CoordinatePoint) : ℝ :=
  ehComputedSourceDensity kappa Lambda (sourceMetric a) i p + actualSourceDensityCoordinates a u i p

theorem same_total_ray_actual_derivative (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u)
    (protocol : ScalarMetricRayProtocol a) :
    HasDerivAt (sameTotalRayAction a kappa Lambda u protocol)
      (sameTotalMetricLF a kappa Lambda coupling u regular protocol.test) 0 :=
  (eh_original_first_variation_hasDerivAt kappa Lambda coupling (sourceMetric a)
    (source_metric_symmetric a) (source_metric_smooth a)
    (fun p _ => source_metric_determinant_negative a p) protocol.test).add
      (same_action_scalar_metric_derivative a u regular protocol)

theorem total_stationary_iff_actual_lf_zero (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) :
    SameTotalMetricStationary a kappa Lambda u ↔
      ∀ h : MetricSourceProbe (sourceDomain a), sameTotalMetricLF a kappa Lambda coupling u regular h = 0 := by
  constructor
  · intro stationary h
    exact (same_total_ray_actual_derivative a kappa Lambda coupling u regular ⟨h⟩).deriv.symm.trans (stationary ⟨h⟩)
  · intro zero protocol
    exact (same_total_ray_actual_derivative a kappa Lambda coupling u regular protocol).deriv.trans (zero protocol.test)

theorem total_actual_density_continuous (a : Parameters) (kappa Lambda : ℝ)
    (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin 10) :
    Continuous (totalActualDensity a kappa Lambda u i) := by
  have geometric : Continuous (ehComputedSourceDensity kappa Lambda (sourceMetric a) i) :=
    continuous_iff_continuousAt.mpr (fun p =>
      (eh_computed_source_density_smooth_at kappa Lambda (sourceMetric a) (source_metric_smooth a)
        p (source_metric_determinant_negative a p) i).continuousAt)
  exact geometric.add (actual_source_density_smooth a u regular i).continuous

theorem total_action_source_representation (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u)
    (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
    representedMetricSource (sameTotalMetricLF a kappa Lambda coupling u (scalarSmoothTwo u regular)) i psi =
      ∫ p, totalActualDensity a kappa Lambda u i p * psi p := by
  have geometric : Continuous (ehComputedSourceDensity kappa Lambda (sourceMetric a) i) :=
    continuous_iff_continuousAt.mpr (fun p =>
      (eh_computed_source_density_smooth_at kappa Lambda (sourceMetric a) (source_metric_smooth a)
        p (source_metric_determinant_negative a p) i).continuousAt)
  have iEH : Integrable (fun p => ehComputedSourceDensity kappa Lambda (sourceMetric a) i p * psi p) :=
    (geometric.mul psi.contDiff.continuous).integrable_of_hasCompactSupport psi.hasCompactSupport.mul_left
  have iMatter : Integrable (fun p => actualSourceDensityCoordinates a u i p * psi p) :=
    ((actual_source_density_smooth a u regular i).continuous.mul psi.contDiff.continuous).integrable_of_hasCompactSupport
      psi.hasCompactSupport.mul_left
  have linear : representedMetricSource (sameTotalMetricLF a kappa Lambda coupling u (scalarSmoothTwo u regular)) i psi =
      originalEHEulerResponse kappa Lambda coupling (sourceMetric a) (source_metric_symmetric a)
        (source_metric_smooth a) (fun p _ => source_metric_determinant_negative a p) i psi +
      sameActionScalarSource a u (scalarSmoothTwo u regular) i psi := by
    simp [sameTotalMetricLF, sameEHMetricLF, originalEHEulerResponse, sameActionScalarSource,
      representedMetricSource, mul_add]
  rw [linear, eh_original_euler_response_density, same_action_source_represents_actual_stress]
  unfold totalActualDensity
  simp_rw [add_mul]
  exact (integral_add iEH iMatter).symm

theorem total_stationary_iff_pointwise_density (a : Parameters) (kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u) :
    SameTotalMetricStationary a kappa Lambda u ↔
      ∀ p ∈ sourceDomain a, ∀ i : Fin 10, totalActualDensity a kappa Lambda u i p = 0 := by
  rw [total_stationary_iff_actual_lf_zero a kappa Lambda coupling u (scalarSmoothTwo u regular)]
  constructor
  · intro zero p inside i
    apply continuous_scalar_source_tests_separate (sourceDomain a) _
      (total_actual_density_continuous a kappa Lambda u regular i) _ p inside
    intro psi
    rw [← total_action_source_representation a kappa Lambda coupling u regular i psi]
    simp [representedMetricSource, zero]
  · intro pointwise h
    have components (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
        representedMetricSource (sameTotalMetricLF a kappa Lambda coupling u (scalarSmoothTwo u regular)) i psi = 0 := by
      rw [total_action_source_representation a kappa Lambda coupling u regular i psi]
      apply integral_eq_zero_of_ae
      apply Eventually.of_forall
      intro p
      change totalActualDensity a kappa Lambda u i p * psi p = 0
      by_cases inside : p ∈ sourceDomain a
      · rw [pointwise p inside i, zero_mul]
      · have zeroPsi : psi p = 0 := by
          by_contra nonzero
          exact inside (psi.tsupport_subset (subset_tsupport psi nonzero))
        rw [zeroPsi, mul_zero]
    rw [← constructed_metric_source_represents]
    simp only [metricSourcePairing, components, mul_zero, Finset.sum_const_zero]

end AASCKleinGordon.SameActionSource
