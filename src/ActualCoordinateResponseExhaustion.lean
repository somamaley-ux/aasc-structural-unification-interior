import OriginalCoordinateCurvatureIdentification
import AdmissibleMetricResponseCore

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

/-- The original actual connection curvature expressed in the supplied
orthonormal frame. Its algebraic laws are proved through the constructed chart. -/
def framedActualConnectionCurvature (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) : curvatureSpace :=
  ⟨pullbackFour (coordinateFrameMatrix B) (loweredConnectionCurvature g (leviCivitaCoefficients g) p), by
    rw [← c2_normalChartCurvature_eq_actual_pullback g p B symmetric regular frame]
    exact (c2_normalChartCurvature g p B symmetric regular frame).property⟩

theorem framedActualConnectionCurvature_eq_normal_chart (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    framedActualConnectionCurvature g p B symmetric regular frame =
      c2_normalChartCurvature g p B symmetric regular frame :=
  Subtype.ext (c2_normalChartCurvature_eq_actual_pullback g p B symmetric regular frame).symm

/-- Arbitrary semantic metric-field response, corrected invertible-comparison
core, C² metric inputs, and original actual Levi-Civita curvature. Original
physical domain coverage, closed-source Ward and active-response locking are
not assumed as hidden fields or declared completed by this theorem. -/
theorem admissible_c2_actual_coordinate_response_exhaustion (E : MetricFieldResponse)
    (core : AdmissibleMetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
        (frame : LorentzFrameAt g p B),
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
        coefficients.1 • ricciResponse (framedActualConnectionCurvature g p B symmetric regular frame) +
          coefficients.2.1 • scalarMetricResponse (framedActualConnectionCurvature g p B symmetric regular frame) +
            coefficients.2.2 • metric := by
  simpa only [framedActualConnectionCurvature_eq_normal_chart] using
    admissible_c2_metric_response_normal_chart_envelope_exhaustion E core

#print axioms framedActualConnectionCurvature_eq_normal_chart
#print axioms admissible_c2_actual_coordinate_response_exhaustion
end
end AASCSemanticExhaustion
