import SKGCompactWard

/-! The constructed source on compact receiving tests is independent of
global extensions. The compared fields have the stated global C2 regularity;
equality is needed only on the open support region of the actual test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem scalar_stress_local (a : Parameters) (F G : CoordinatePoint → ℝ)
    (W : Opens CoordinatePoint) (same : EqOn F G W) (p : CoordinatePoint) (inside : p ∈ W) :
    sameSourceStress a F p = sameSourceStress a G p := by
  have near : F =ᶠ[𝓝 p] G := by
    filter_upwards [W.isOpen.mem_nhds inside] with q hq
    exact same hq
  have gradient : scalarPartial F p = scalarPartial G p := by
    funext i
    exact congrArg (fun L : CoordinatePoint →L[ℝ] ℝ => L (Pi.single i 1)) near.fderiv_eq
  ext i j
  simp only [sameSourceStress, scalarFieldStress, scalarFieldKinetic, gradient, same inside]

theorem scalar_density_local (a : Parameters) (F G : CoordinatePoint → ℝ)
    (W : Opens CoordinatePoint) (same : EqOn F G W) (p : CoordinatePoint) (inside : p ∈ W) (i : Fin 10) :
    actualSourceDensityCoordinates a F i p = actualSourceDensityCoordinates a G i p := by
  change raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a F) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 =
    raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a G) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2
  rw [same_source_raised_density, same_source_raised_density, scalar_stress_local a F G W same p inside]

theorem scalar_source_local_component (a : Parameters) (F G : CoordinatePoint → ℝ)
    (regularF : ContDiff ℝ 2 F) (regularG : ContDiff ℝ 2 G)
    (W : Opens CoordinatePoint) (same : EqOn F G W) (i : Fin 10)
    (psi : ScalarSourceProbe (sourceDomain a)) (supported : ∀ p, psi p ≠ 0 → p ∈ W) :
    sameActionScalarSource a F regularF i psi = sameActionScalarSource a G regularG i psi := by
  rw [same_action_source_represents_actual_stress, same_action_source_represents_actual_stress]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  change actualSourceDensityCoordinates a F i p * psi p = actualSourceDensityCoordinates a G i p * psi p
  by_cases zero : psi p = 0
  · simp [zero]
  · rw [scalar_density_local a F G W same p (supported p zero) i]

theorem scalar_response_local (a : Parameters) (F G : CoordinatePoint → ℝ)
    (regularF : ContDiff ℝ 2 F) (regularG : ContDiff ℝ 2 G)
    (W : Opens CoordinatePoint) (same : EqOn F G W)
    (h : MetricSourceProbe (sourceDomain a)) (supported : tsupport h ⊆ W) :
    sameActionScalarMetricLF a F regularF h = sameActionScalarMetricLF a G regularG h := by
  rw [← constructed_metric_source_represents (sameActionScalarMetricLF a F regularF) h,
    ← constructed_metric_source_represents (sameActionScalarMetricLF a G regularG) h]
  congr 1
  unfold metricSourcePairing
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply scalar_source_local_component a F G regularF regularG W same i
  intro p nonzero
  change h p i ≠ 0 at nonzero
  have fullNonzero : h p ≠ 0 := by
    intro zero
    apply nonzero
    rw [zero]
    rfl
  exact supported (subset_tsupport h fullNonzero)

theorem scalar_ray_output_local (a : Parameters) (F G : CoordinatePoint → ℝ)
    (regularF : ContDiff ℝ 2 F) (regularG : ContDiff ℝ 2 G)
    (W : Opens CoordinatePoint) (same : EqOn F G W)
    (protocol : ScalarMetricRayProtocol a) (supported : tsupport protocol.test ⊆ W) :
    scalarMetricRayOutput a F protocol = scalarMetricRayOutput a G protocol := by
  rw [same_action_ray_output_is_constructed_response a F regularF,
    same_action_ray_output_is_constructed_response a G regularG]
  exact scalar_response_local a F G regularF regularG W same protocol.test supported

end AASCKleinGordon.SameActionSource
