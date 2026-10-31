import LorentzFrameContractions

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

/-- The arbitrary response is exhausted in the original coordinate field,
using its actual inverse-metric contractions and connection curvature. Frames
occur only as the explicitly supplied Lorentzian projection anchor. -/
theorem admissible_c2_coordinate_metric_response_normal_form (E : MetricFieldResponse)
    (core : AdmissibleMetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
        (frame : LorentzFrameAt g p B),
      E g p = coefficients.1 • coordinateRicci g p +
        coefficients.2.1 • coordinateScalarMetric g p + coefficients.2.2 • g p := by
  simpa only [actual_coordinate_response_identity_iff] using
    admissible_c2_actual_coordinate_response_exhaustion E core

#print axioms admissible_c2_coordinate_metric_response_normal_form
end
end AASCSemanticExhaustion
