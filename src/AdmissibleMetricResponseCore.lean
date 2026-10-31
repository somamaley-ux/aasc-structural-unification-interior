import GeneralMetricNormalizingCurvature

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

/-- Naturality only for actual local diffeomorphisms. Invertibility of the
derivative is explicit; the inverse function theorem constructs the local inverse. -/
def MetricResponseDiffeomorphismNatural (E : MetricFieldResponse) : Prop :=
  ∀ (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    ContDiffAt ℝ ⊤ F p → HasFDerivAt F B.toContinuousLinearMap p → ∀ g,
      E (coordinateMetricPullback g F) p =
        (coordinateJacobian F p).transpose * E g (F p) * coordinateJacobian F p

def AdmissibleMetricFirstResponseCore (E : MetricFieldResponse) : Prop :=
  MetricResponseDiffeomorphismNatural E ∧ MetricTwoJetLocal E ∧
    MetricFirstResponseAffine E ∧ MetricResponseSymmetric E

theorem diffeomorphism_naturality_hessian_gauge (E : MetricFieldResponse)
    (natural : MetricResponseDiffeomorphismNatural E) (localOrder : MetricTwoJetLocal E) :
    HessianGaugeInvariant (metricHessianResponseAt E 0) := by
  intro H K hK
  obtain ⟨T, laws, gauge⟩ := hK
  have hjet := cubic_gauge_actual_twojet H K T laws gauge
  have heq := localOrder _ _ 0 hjet
  have hn := natural (cubicCoordinateMap (raisedCubicCoordinate T)) 0
    (ContinuousLinearEquiv.refl ℝ CoordinatePoint) (cubicCoordinateMap_smooth _).contDiffAt
      (cubicCoordinateMap_hasFDerivAt_zero _) (hessianMetricPolynomial H)
  rw [cubic_coordinate_jacobian_zero _ (raisedCubicCoordinate_laws T laws), cubicCoordinateMap_zero] at hn
  simp only [Matrix.transpose_one, one_mul, mul_one] at hn
  rw [metricHessianResponseAt_origin, metricHessianResponseAt_origin]
  exact heq.symm.trans hn

theorem diffeomorphism_naturality_hessian_covariance (E : MetricFieldResponse)
    (natural : MetricResponseDiffeomorphismNatural E) (localOrder : MetricTwoJetLocal E) :
    HessianCovariant (metricHessianResponseAt E 0) := by
  intro L H K transport
  have heq := localOrder _ _ 0 (lorentz_frame_actual_twojet L H K transport)
  have hn := natural (lorentzCoordinateMap L) 0 (lorentzCoordinateEquiv L)
    (lorentzCoordinateMap_smooth L).contDiffAt (lorentzCoordinateMap_hasFDerivAt L 0)
      (hessianMetricPolynomial H)
  rw [lorentzCoordinateMap_jacobian, lorentzCoordinateMap_zero] at hn
  rw [metricHessianResponseAt_origin, metricHessianResponseAt_origin]
  exact heq.symm.trans hn

theorem admissible_metric_response_jet_exhaustion (E : MetricFieldResponse)
    (core : AdmissibleMetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ H : metricHessianSpace,
      E (hessianMetricPolynomial H) 0 = coefficients.1 • ricciResponse (curvatureJetMap H) +
        coefficients.2.1 • scalarMetricResponse (curvatureJetMap H) + coefficients.2.2 • metric := by
  simpa only [metricHessianResponseAt_origin] using
    hessian_response_unique_normal_form (metricHessianResponseAt E 0)
      (metric_response_hessian_affine_from_first_response E core.2.2.1)
      (metric_response_hessian_symmetric E core.2.2.2)
      (diffeomorphism_naturality_hessian_covariance E core.1 core.2.1)
      (diffeomorphism_naturality_hessian_gauge E core.1 core.2.1)

theorem admissible_c2_normalized_metric_response_exhaustion (E : MetricFieldResponse)
    (core : AdmissibleMetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ g : MetricField, ∀ germ : C2NormalizedMetricGerm g,
      E g 0 = coefficients.1 • ricciResponse (c2NormalizedLeviCivitaCurvature g germ) +
        coefficients.2.1 • scalarMetricResponse (c2NormalizedLeviCivitaCurvature g germ) +
          coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := admissible_metric_response_jet_exhaustion E core
  refine ⟨coefficients, ?_, ?_⟩
  · intro g germ
    rw [core.2.1 g _ 0 (c2_normalized_metric_matches_receiver g germ),
      c2_normalizedLeviCivitaCurvature_eq_jet]
    exact h (c2MetricHessian g 0 germ.1 germ.2.1)
  · intro other ho
    apply unique other
    intro H
    have hh := ho (hessianMetricPolynomial H) (hessianMetricPolynomial_c2_normalized H)
    simpa only [c2_normalizedLeviCivitaCurvature_eq_jet, c2NormalizedMetricJetCurvature_receiver] using hh

theorem diffeomorphism_natural_response_point_normal_chart (E : MetricFieldResponse)
    (natural : MetricResponseDiffeomorphismNatural E) (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    E (pointNormalizedMetric g p B) 0 =
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B := by
  have h := natural (pointNormalChartMap g p B) 0 B (pointNormalChartMap_analytic g p B).contDiffAt
    (pointNormalChartMap_hasFDerivAt g p B symmetric) g
  simpa only [pointNormalChartMap_pullback, pointNormalChartMap_zero,
    pointNormalChartMap_jacobian g p B symmetric] using h

/-- The response exhaustion on the intended invertible-comparison candidate
class, with actual C² metric curvature and one coordinate-envelope coefficient triple. -/
theorem admissible_c2_metric_response_normal_chart_envelope_exhaustion (E : MetricFieldResponse)
    (core : AdmissibleMetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
        (frame : LorentzFrameAt g p B),
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
        coefficients.1 • ricciResponse (c2_normalChartCurvature g p B symmetric regular frame) +
          coefficients.2.1 • scalarMetricResponse (c2_normalChartCurvature g p B symmetric regular frame) +
            coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := admissible_c2_normalized_metric_response_exhaustion E core
  refine ⟨coefficients, ?_, ?_⟩
  · intro g p B symmetric regular frame
    have hc := h (pointNormalizedMetric g p B) (c2_pointNormalizedMetric_germ g p B symmetric regular frame)
    exact (diffeomorphism_natural_response_point_normal_chart E core.1 g p B symmetric).symm.trans hc
  · intro other ho
    apply unique other
    intro g germ
    have hh := ho g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) germ.1 germ.2.1
      (c2_normalizedMetric_identity_frame g germ)
    simpa only [coordinateFrameMatrix_refl, Matrix.transpose_one, one_mul, mul_one,
      c2_normalChartCurvature_retraction g germ] using hh

#print axioms diffeomorphism_naturality_hessian_gauge
#print axioms diffeomorphism_naturality_hessian_covariance
#print axioms admissible_metric_response_jet_exhaustion
#print axioms admissible_c2_normalized_metric_response_exhaustion
#print axioms diffeomorphism_natural_response_point_normal_chart
#print axioms admissible_c2_metric_response_normal_chart_envelope_exhaustion
end
end AASCSemanticExhaustion
