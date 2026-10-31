import SKGScalarExchange

/-! Each actual action-sector derivative represents its own actual stress.
The stress split is thereby attached to the one-time action registry. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

theorem kinetic_action_source_represents_actual_stress (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
    representedMetricSource (kineticScalarMetricLF a u regular) i psi =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a)
        (kineticScalarStress a u)) i p * psi p := by
  unfold kineticScalarMetricLF nativeScalarClockMetricLF
  rw [native_clock_constructed_source_integral_components]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    change nativeClockSourceCoefficient (sourceMetric a) (nativeScalarClockGradient u) u 0 i p * psi p = _
    rw [scalar_clock_coefficient_is_raised_density_of_negative (sourceMetric a)
      (source_metric_symmetric a) u 0 p (source_metric_determinant_negative a p) i]
    rfl)

theorem kinetic_source_density_continuous (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin 10) :
    Continuous (fun p => sourceDensityCoordinates
      (raisedSourceTensorDensity (sourceMetric a) (kineticScalarStress a u)) i p) := by
  have same : (fun p => sourceDensityCoordinates
      (raisedSourceTensorDensity (sourceMetric a) (kineticScalarStress a u)) i p) = fun p =>
      (metric (sourceSymmetricPair i).1 (sourceSymmetricPair i).1 *
        metric (sourceSymmetricPair i).2 (sourceSymmetricPair i).2) *
      kineticScalarStress a u p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 :=
    funext (fun p => same_source_raised_density a _ p _ _)
  rw [same]
  exact continuous_const.mul (kinetic_scalar_stress_smooth a u regular _ _).continuous

theorem mass_action_source_represents_actual_stress (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin 10) (psi : ScalarSourceProbe (sourceDomain a)) :
    representedMetricSource (massScalarMetricLF a u (scalarSmoothTwo u regular)) i psi =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (sourceMetric a)
        (massScalarStress a u)) i p * psi p := by
  have linear : representedMetricSource (massScalarMetricLF a u (scalarSmoothTwo u regular)) i psi =
      sameActionScalarSource a u (scalarSmoothTwo u regular) i psi -
      representedMetricSource (kineticScalarMetricLF a u (scalarSmoothTwo u regular)) i psi := by
    simp [massScalarMetricLF, sameActionScalarSource, representedMetricSource, mul_sub]
  rw [linear, same_action_source_represents_actual_stress, kinetic_action_source_represents_actual_stress]
  have iTotal : Integrable (fun p => sourceDensityCoordinates
      (raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u)) i p * psi p) :=
    ((actual_source_density_smooth a u regular i).continuous.mul psi.contDiff.continuous).integrable_of_hasCompactSupport
      psi.hasCompactSupport.mul_left
  have iKinetic : Integrable (fun p => sourceDensityCoordinates
      (raisedSourceTensorDensity (sourceMetric a) (kineticScalarStress a u)) i p * psi p) :=
    ((kinetic_source_density_continuous a u regular i).mul psi.contDiff.continuous).integrable_of_hasCompactSupport
      psi.hasCompactSupport.mul_left
  rw [← integral_sub iTotal iKinetic]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  change raisedSourceTensorDensity (sourceMetric a) (sameSourceStress a u) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 * psi p -
    raisedSourceTensorDensity (sourceMetric a) (kineticScalarStress a u) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 * psi p =
    raisedSourceTensorDensity (sourceMetric a) (massScalarStress a u) p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 * psi p
  rw [same_source_raised_density, same_source_raised_density, same_source_raised_density,
    scalar_actual_stress_kinetic_mass_split]
  change _ * (_ + _) * psi p - _ = _
  ring

theorem actual_sector_source_reader_square (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a) :
    HasDerivAt (kineticScalarRayAction a u protocol)
      ((1 / 2 : ℝ) * metricSourcePairing (representedMetricSource (kineticScalarMetricLF a u regular)) protocol.test) 0 ∧
    HasDerivAt (massScalarRayAction a u protocol)
      ((1 / 2 : ℝ) * metricSourcePairing (representedMetricSource (massScalarMetricLF a u regular)) protocol.test) 0 := by
  simp only [constructed_metric_source_represents]
  exact ⟨kinetic_scalar_action_actual_derivative a u regular protocol,
    mass_scalar_action_actual_derivative a u regular protocol⟩

end AASCKleinGordon.SameActionSource
