import FirstMetricResponseLaws
import MetricResponseFrameCovariance

/-!
An arbitrary response to actual metric fields, with explicit local order,
naturality, symmetry and affine first-response laws. The Hessian response,
frame covariance and cubic-gauge invariance are derived, not completeness
fields. This is the coordinate-germ core of the manuscript's first-response
exhaustion; full projection-envelope interpretation, S17/S18 and normalization
of arbitrary charts are separate obligations.
-/
namespace AASCSemanticExhaustion
noncomputable section

def MetricFirstResponseCore (E : MetricFieldResponse) : Prop :=
  MetricResponseNatural E ∧ MetricTwoJetLocal E ∧
    MetricFirstResponseAffine E ∧ MetricResponseSymmetric E

def normalizedMetricJetCurvature (g : MetricField) (germ : NormalizedSmoothMetricGerm g) : curvatureSpace :=
  curvatureJetMap (actualMetricHessian g 0 germ.1 germ.2.1)

theorem normalizedMetricJetCurvature_receiver (H : metricHessianSpace) :
    normalizedMetricJetCurvature (hessianMetricPolynomial H) (hessianMetricPolynomial_normalized H) =
      curvatureJetMap H := by
  apply congrArg curvatureJetMap
  apply Subtype.ext
  funext a b c d
  exact hessian_metric_scalarSecond H a b c d

theorem metric_field_response_jet_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ H : metricHessianSpace,
      E (hessianMetricPolynomial H) 0 = coefficients.1 • ricciResponse (curvatureJetMap H) +
        coefficients.2.1 • scalarMetricResponse (curvatureJetMap H) + coefficients.2.2 • metric := by
  obtain ⟨natural, localOrder, affine, symmetric⟩ := core
  simpa only [metricHessianResponseAt_origin] using
    hessian_response_unique_normal_form (metricHessianResponseAt E 0)
      (metric_response_hessian_affine_from_first_response E affine)
      (metric_response_hessian_symmetric E symmetric)
      (metric_response_hessian_covariant_from_naturality E natural localOrder)
      (metric_response_hessian_gauge_from_naturality E natural localOrder)

theorem metric_field_response_normalized_germ_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ g : MetricField, ∀ germ : NormalizedSmoothMetricGerm g,
      E g 0 = coefficients.1 • ricciResponse (normalizedMetricJetCurvature g germ) +
        coefficients.2.1 • scalarMetricResponse (normalizedMetricJetCurvature g germ) +
          coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := metric_field_response_jet_exhaustion E core
  refine ⟨coefficients, ?_, ?_⟩
  · intro g germ
    rw [metric_response_normalized_jet_factorization E core.2.1 g germ.1 germ.2.1
      germ.2.2.1 germ.2.2.2]
    exact h (actualMetricHessian g 0 germ.1 germ.2.1)
  · intro other ho
    apply unique other
    intro H
    have hh := ho (hessianMetricPolynomial H) (hessianMetricPolynomial_normalized H)
    simpa only [normalizedMetricJetCurvature_receiver] using hh

theorem metric_field_response_translated_coefficients_constant (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ p : CoordinatePoint, ∀ H : metricHessianSpace,
      E (fun x => hessianMetricPolynomial H (x - p)) p =
        coefficients.1 • ricciResponse (curvatureJetMap H) +
          coefficients.2.1 • scalarMetricResponse (curvatureJetMap H) + coefficients.2.2 • metric := by
  obtain ⟨natural, localOrder, affine, symmetric⟩ := core
  exact translated_metric_response_coefficients_constant E natural
    (metric_response_hessian_affine_from_first_response E affine)
    (metric_response_hessian_symmetric E symmetric)
    (metric_response_hessian_covariant_from_naturality E natural localOrder)
    (metric_response_hessian_gauge_from_naturality E natural localOrder)

#print axioms normalizedMetricJetCurvature_receiver
#print axioms metric_field_response_jet_exhaustion
#print axioms metric_field_response_normalized_germ_exhaustion
#print axioms metric_field_response_translated_coefficients_constant
end
end AASCSemanticExhaustion
