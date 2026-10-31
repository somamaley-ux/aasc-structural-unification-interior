import SKGCompactWard

/-! A one-time kinetic/mass action registry. Each response is an actual
ordinary derivative; the mass response is not an arbitrary tensor addition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open AASCKleinGordon.CurvedKG
open scoped Topology BigOperators
namespace AASCKleinGordon.SameActionSource

def kineticScalarRayAction (a : Parameters) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) (t : ℝ) : ℝ :=
  nativeScalarClockRelativeAction (sourceMetric a) u 0 (t • protocol.test)

def massScalarRayAction (a : Parameters) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) (t : ℝ) : ℝ :=
  scalarMetricRayAction a u protocol t - kineticScalarRayAction a u protocol t

def kineticScalarMetricLF (a : Parameters) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) :
    MetricSourceProbe (sourceDomain a) →L[ℝ] ℝ :=
  nativeScalarClockMetricLF (sourceMetric a) u 0 (source_metric_continuous a) regular
    (fun p _ => source_metric_nondegenerate a p)

def massScalarMetricLF (a : Parameters) (u : CoordinatePoint → ℝ) (regular : ContDiff ℝ 2 u) :
    MetricSourceProbe (sourceDomain a) →L[ℝ] ℝ :=
  sameActionScalarMetricLF a u regular - kineticScalarMetricLF a u regular

def kineticScalarStress (a : Parameters) (u : CoordinatePoint → ℝ) : MetricField :=
  scalarFieldStress (sourceMetric a) u 0

def massScalarStress (a : Parameters) (u : CoordinatePoint → ℝ) : MetricField :=
  fun p i j => -(1 / 2 : ℝ) * (massWaveNumber a ^ 2) * u p ^ 2 * sourceMetric a p i j

theorem scalar_actual_action_kinetic_mass_split (a : Parameters) (u : CoordinatePoint → ℝ)
    (protocol : ScalarMetricRayProtocol a) (t : ℝ) :
    scalarMetricRayAction a u protocol t =
      kineticScalarRayAction a u protocol t + massScalarRayAction a u protocol t := by
  unfold massScalarRayAction
  ring

theorem kinetic_scalar_action_actual_derivative (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a) :
    HasDerivAt (kineticScalarRayAction a u protocol) (kineticScalarMetricLF a u regular protocol.test) 0 :=
  native_scalar_clock_action_derivative_constructed (sourceMetric a) (source_metric_symmetric a)
    u 0 (source_metric_continuous a) regular (fun p _ => source_metric_nondegenerate a p) protocol.test

theorem mass_scalar_action_actual_derivative (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) (protocol : ScalarMetricRayProtocol a) :
    HasDerivAt (massScalarRayAction a u protocol) (massScalarMetricLF a u regular protocol.test) 0 :=
  (same_action_scalar_metric_derivative a u regular protocol).sub
    (kinetic_scalar_action_actual_derivative a u regular protocol)

theorem scalar_actual_source_kinetic_mass_split (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) :
    sameActionScalarMetricLF a u regular = kineticScalarMetricLF a u regular + massScalarMetricLF a u regular := by
  unfold massScalarMetricLF
  module

theorem scalar_actual_stress_kinetic_mass_split (a : Parameters) (u : CoordinatePoint → ℝ) :
    sameSourceStress a u = kineticScalarStress a u + massScalarStress a u := by
  funext p i j
  simp only [sameSourceStress, kineticScalarStress, massScalarStress, scalarFieldStress,
    Pi.add_apply, Matrix.add_apply, zero_mul, add_zero]
  ring

theorem scalar_actual_density_kinetic_mass_split (G : NativeRealMatrix) (v : Fin 4 → ℝ)
    (phi mu2 : ℝ) :
    nativeRealClockDensity G v phi mu2 = nativeRealClockDensity G v phi 0 +
      (-(1 / 2 : ℝ) * nativeRealClockVolume G * mu2 * phi ^ 2) := by
  unfold nativeRealClockDensity
  ring

theorem represented_scalar_source_kinetic_mass_split (a : Parameters) (u : CoordinatePoint → ℝ)
    (regular : ContDiff ℝ 2 u) :
    sameActionScalarSource a u regular =
      representedMetricSource (kineticScalarMetricLF a u regular) +
        representedMetricSource (massScalarMetricLF a u regular) := by
  rw [sameActionScalarSource, scalar_actual_source_kinetic_mass_split a u regular]
  funext i
  ext psi
  simp [representedMetricSource]

end AASCKleinGordon.SameActionSource
