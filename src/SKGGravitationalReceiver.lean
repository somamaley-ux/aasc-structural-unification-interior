import SKGSourcedEinstein

/-! The existing licensed EH source receiver is evaluated on the very
same metric and compact test. In the covariant-metric convention its source
is the negative of matter on a stationary total action. No quantum-source
identification or coupled-development existence is asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG AASCKleinGordon.CanonicalLicensing
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def liftSourceScalarTest (a : Parameters) (psi : ScalarSourceProbe (sourceDomain a)) :
    ScalarSourceProbe (⊤ : Opens CoordinatePoint) :=
  ⟨psi, psi.contDiff, psi.hasCompactSupport, by intro p hp; trivial⟩

theorem licensed_eh_receiver_is_negative_actual_matter_source (a : Parameters) (s kappa Lambda : ℝ)
    (coupling : kappa ≠ 0) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) u)
    (stationary : SameTotalMetricStationary a kappa Lambda u)
    (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
    restrictedEHKernelSource a s (⊤ : Opens CoordinatePoint) kappa Lambda coupling
      (licensedEHSourceProfile a s (⊤ : Opens CoordinatePoint)
        (curvedLicensedMetricReceiver a s kappa Lambda coupling)) i (liftSourceScalarTest a psi) =
      -sameActionScalarSource a u (scalarSmoothTwo u regular) i psi := by
  rw [licensed_eh_same_metric_representation a s (⊤ : Opens CoordinatePoint) kappa Lambda coupling,
    curved_licensed_metric_exact a s kappa Lambda coupling,
    same_action_source_represents_actual_stress]
  rw [← integral_neg]
  have pointwise := (total_stationary_iff_pointwise_density a kappa Lambda coupling u regular).mp stationary
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  change sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a)
      (originalEHGeometricResponse kappa Lambda (sourceMetric a))) i p * psi p =
    -(actualSourceDensityCoordinates a u i p * psi p)
  rw [← same_eh_component_density]
  by_cases zero : psi p = 0
  · simp [zero]
  · have inside := psi.tsupport_subset (subset_tsupport psi zero)
    have balance := pointwise p inside i
    change ehComputedSourceDensity kappa Lambda (sourceMetric a) i p + actualSourceDensityCoordinates a u i p = 0 at balance
    have identified : ehComputedSourceDensity kappa Lambda (sourceMetric a) i p =
        -actualSourceDensityCoordinates a u i p := by linarith
    rw [identified]
    ring

end AASCKleinGordon.SameActionSource
