import WickCompactCurveProtocols
import KGNativeWickRayOperationalSource

/-! The enlarged actual finite-action receiver has the SAME original LF
source, on every actual unit representative. Completeness here concerns only
this explicitly declared analytic receiver, not the upstream original ledger. -/
noncomputable section
set_option maxHeartbeats 1000000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_compact_curve_operational_compact_continuity (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint)
    (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint)⊆Ω) :
    Continuous (operationalMetricResponse (wickCompactCurveMetricIncidence a s u Ω) ∘
      TestFunction.ofSupportedIn hK) := by
  have heq : operationalMetricResponse (wickCompactCurveMetricIncidence a s u Ω)=
      originalWickNativeRealMetricResponse a s u Ω :=
    funext (wick_compact_curve_operational_response_is_original a s u Ω)
  rw [heq]
  exact (originalWickNativeRealMetricResponse a s u Ω).continuous.comp
    (TestFunction.continuous_ofSupportedIn hK)

theorem wick_compact_curve_LF_functional_is_original (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    operationalMetricFunctional (wickCompactCurveMetricIncidence a s u Ω)
      (wick_compact_curve_operational_compact_continuity a s u Ω)=
      originalWickNativeRealMetricResponse a s u Ω := by
  apply ContinuousLinearMap.ext
  intro H
  exact wick_compact_curve_operational_response_is_original a s u Ω H

def wickRayCompactCurveMetricIncidence (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) : OperationalMetricIncidence Ω (WickCompactC1MetricCurve Ω) :=
  wickCompactCurveMetricIncidence a s (originalWickUnitRepresentative a ray.out.val) Ω

theorem original_wick_ray_compact_curve_operational_response (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    operationalMetricResponse (wickRayCompactCurveMetricIncidence a s Ω ray) H=
      originalWickRayMetricResponse a s Ω ray H := by
  unfold wickRayCompactCurveMetricIncidence
  rw [wick_compact_curve_operational_response_is_original]
  have hu := original_wick_ray_source_is_actual_unit_response a s Ω ray.out
  rw [Quotient.out_eq] at hu
  exact (congrArg (fun W : MetricSourceProbe Ω →L[ℝ] ℝ => W H) hu).symm

theorem original_wick_ray_compact_curve_response_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid)
    (H : MetricSourceProbe Ω) (z : ℝ) :
    originalWickRayMetricResponse a s Ω ray H=z ↔
      ∃ π : WickCompactC1MetricCurve Ω,
        (wickRayCompactCurveMetricIncidence a s Ω ray).incident H π ∧
          (wickRayCompactCurveMetricIncidence a s Ω ray).output π=z := by
  rw [← original_wick_ray_compact_curve_operational_response a s Ω ray H]
  exact operational_response_graph _ H z

end AASCKleinGordon
