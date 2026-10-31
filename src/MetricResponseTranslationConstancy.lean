import CoordinateMetricNaturality
import HessianResponseExhaustion

namespace AASCSemanticExhaustion
noncomputable section

def metricHessianResponseAt (E : MetricFieldResponse) (p : CoordinatePoint)
    (H : metricHessianSpace) : Tensor2 :=
  E (fun x => hessianMetricPolynomial H (x - p)) p

theorem metricHessianResponseAt_origin (E : MetricFieldResponse) (H : metricHessianSpace) :
    metricHessianResponseAt E 0 H = E (hessianMetricPolynomial H) 0 := by
  simp [metricHessianResponseAt]

theorem metricHessianResponseAt_translation (E : MetricFieldResponse)
    (natural : MetricResponseNatural E) (p : CoordinatePoint) (H : metricHessianSpace) :
    metricHessianResponseAt E p H = metricHessianResponseAt E 0 H := by
  have h := metric_response_translation E natural (hessianMetricPolynomial H) p (-p)
  simpa [metricHessianResponseAt, sub_eq_add_neg] using h

/-- One coefficient triple for all translated normalized metric-jet tests.
The hypotheses on the origin response remain explicit until derived from the
original candidate's order and coordinate-naturality laws. -/
theorem translated_metric_response_coefficients_constant (E : MetricFieldResponse)
    (natural : MetricResponseNatural E)
    (affine : HessianAffine (metricHessianResponseAt E 0))
    (symmetric : HessianSymmetric (metricHessianResponseAt E 0))
    (covariant : HessianCovariant (metricHessianResponseAt E 0))
    (gauge : HessianGaugeInvariant (metricHessianResponseAt E 0)) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ p : CoordinatePoint, ∀ H : metricHessianSpace,
      metricHessianResponseAt E p H = coefficients.1 • ricciResponse (curvatureJetMap H) +
        coefficients.2.1 • scalarMetricResponse (curvatureJetMap H) + coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := hessian_response_unique_normal_form
    (metricHessianResponseAt E 0) affine symmetric covariant gauge
  refine ⟨coefficients, ?_, ?_⟩
  · intro p H
    rw [metricHessianResponseAt_translation E natural p H]
    exact h H
  · intro other ho
    exact unique other (ho 0)

#print axioms metricHessianResponseAt_origin
#print axioms metricHessianResponseAt_translation
#print axioms translated_metric_response_coefficients_constant
end
end AASCSemanticExhaustion
