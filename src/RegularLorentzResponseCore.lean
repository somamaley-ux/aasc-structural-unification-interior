import CoordinateMetricResponseNormalForm

/-! Regular Lorentzian domain of the response laws. No condition is imposed on
values at rough, nonsymmetric or non-Lorentzian fields. This is a new receiver,
not a replacement of the original manuscript predicate. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def C2LorentzMetricAt (g : MetricField) (p : CoordinatePoint) : Prop :=
  MetricFieldSymmetric g ∧ (∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) ∧
    ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint, LorentzFrameAt g p B

def RegularLorentzResponseNatural (E : MetricFieldResponse) : Prop :=
  ∀ (F : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint),
    ContDiffAt ℝ ⊤ F p → HasFDerivAt F B.toContinuousLinearMap p →
    ∀ g, C2LorentzMetricAt g (F p) →
      E (coordinateMetricPullback g F) p =
        (coordinateJacobian F p).transpose * E g (F p) * coordinateJacobian F p

def RegularLorentzTwoJetLocal (E : MetricFieldResponse) : Prop :=
  ∀ g h p, C2LorentzMetricAt g p → C2LorentzMetricAt h p →
    MetricTwoJetEqualAt g h p → E g p = E h p

def RegularLorentzResponseCore (E : MetricFieldResponse) : Prop :=
  RegularLorentzResponseNatural E ∧ RegularLorentzTwoJetLocal E ∧
    MetricFirstResponseAffine E ∧
      ∀ g p, C2LorentzMetricAt g p → ∀ a b, E g p a b = E g p b a

theorem c2_normalized_is_lorentz (g : MetricField) (hg : C2NormalizedMetricGerm g) :
    C2LorentzMetricAt g 0 :=
  ⟨hg.1, hg.2.1, ContinuousLinearEquiv.refl ℝ CoordinatePoint,
    c2_normalizedMetric_identity_frame g hg⟩

theorem hessian_receiver_is_c2_lorentz (H : metricHessianSpace) :
    C2LorentzMetricAt (hessianMetricPolynomial H) 0 :=
  c2_normalized_is_lorentz _ (hessianMetricPolynomial_c2_normalized H)

theorem c2_lorentz_of_normal_value (g : MetricField)
    (hs : MetricFieldSymmetric g)
    (hr : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (hv : g 0=metric) :
    C2LorentzMetricAt g 0 := by
  refine ⟨hs,hr,ContinuousLinearEquiv.refl ℝ CoordinatePoint,?_⟩
  change (coordinateFrameMatrix (ContinuousLinearEquiv.refl ℝ CoordinatePoint)).transpose *
    g 0 * coordinateFrameMatrix (ContinuousLinearEquiv.refl ℝ CoordinatePoint) = metric
  simpa only [coordinateFrameMatrix_refl,Matrix.transpose_one,one_mul,mul_one] using hv

theorem regular_lorentz_hessian_gauge (E : MetricFieldResponse)
    (hn : RegularLorentzResponseNatural E) (hl : RegularLorentzTwoJetLocal E) :
    HessianGaugeInvariant (metricHessianResponseAt E 0) := by
  intro H K hK
  obtain ⟨T,laws,gauge⟩ := hK
  have hjet := cubic_gauge_actual_twojet H K T laws gauge
  have hdom : C2LorentzMetricAt
      (coordinateMetricPullback (hessianMetricPolynomial H) (cubicCoordinateMap (raisedCubicCoordinate T))) 0 := by
    apply c2_lorentz_of_normal_value
    · exact coordinateMetricPullback_symmetric _ (hessianMetricPolynomial_symmetric H) _
    · apply c2_coordinateMetricPullback_contDiffAt _ _ 0 (cubicCoordinateMap_smooth _).contDiffAt
      simpa only [cubicCoordinateMap_zero] using (hessianMetricPolynomial_c2_normalized H).2.1
    · exact hjet.1.trans (hessianMetricPolynomial_zero (H+K))
  have heq := hl _ _ 0 hdom (hessian_receiver_is_c2_lorentz (H+K)) hjet
  have hg : C2LorentzMetricAt (hessianMetricPolynomial H)
      (cubicCoordinateMap (raisedCubicCoordinate T) 0) := by
    simpa only [cubicCoordinateMap_zero] using hessian_receiver_is_c2_lorentz H
  have hc := hn (cubicCoordinateMap (raisedCubicCoordinate T)) 0
    (ContinuousLinearEquiv.refl ℝ CoordinatePoint) (cubicCoordinateMap_smooth _).contDiffAt
      (cubicCoordinateMap_hasFDerivAt_zero _) _ hg
  rw [cubic_coordinate_jacobian_zero _ (raisedCubicCoordinate_laws T laws),cubicCoordinateMap_zero] at hc
  simp only [Matrix.transpose_one,one_mul,mul_one] at hc
  rw [metricHessianResponseAt_origin,metricHessianResponseAt_origin]
  exact heq.symm.trans hc

theorem regular_lorentz_hessian_covariance (E : MetricFieldResponse)
    (hn : RegularLorentzResponseNatural E) (hl : RegularLorentzTwoJetLocal E) :
    HessianCovariant (metricHessianResponseAt E 0) := by
  intro L H K transport
  have hjet := lorentz_frame_actual_twojet L H K transport
  have hdom : C2LorentzMetricAt
      (coordinateMetricPullback (hessianMetricPolynomial H) (lorentzCoordinateMap L)) 0 := by
    apply c2_lorentz_of_normal_value
    · exact coordinateMetricPullback_symmetric _ (hessianMetricPolynomial_symmetric H) _
    · apply c2_coordinateMetricPullback_contDiffAt _ _ 0 (lorentzCoordinateMap_smooth L).contDiffAt
      simpa only [lorentzCoordinateMap_zero] using (hessianMetricPolynomial_c2_normalized H).2.1
    · exact hjet.1.trans (hessianMetricPolynomial_zero K)
  have heq := hl _ _ 0 hdom (hessian_receiver_is_c2_lorentz K) hjet
  have hg : C2LorentzMetricAt (hessianMetricPolynomial H) (lorentzCoordinateMap L 0) := by
    simpa only [lorentzCoordinateMap_zero] using hessian_receiver_is_c2_lorentz H
  have hc := hn (lorentzCoordinateMap L) 0 (lorentzCoordinateEquiv L)
    (lorentzCoordinateMap_smooth L).contDiffAt (lorentzCoordinateMap_hasFDerivAt L 0) _ hg
  rw [lorentzCoordinateMap_jacobian,lorentzCoordinateMap_zero] at hc
  rw [metricHessianResponseAt_origin,metricHessianResponseAt_origin]
  exact heq.symm.trans hc

theorem regular_lorentz_response_jet_exhaustion (E : MetricFieldResponse)
    (core : RegularLorentzResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ H : metricHessianSpace,
      E (hessianMetricPolynomial H) 0 = coefficients.1 • ricciResponse (curvatureJetMap H) +
        coefficients.2.1 • scalarMetricResponse (curvatureJetMap H) + coefficients.2.2 • metric := by
  have hs : HessianSymmetric (metricHessianResponseAt E 0) := by
    intro H a b
    rw [metricHessianResponseAt_origin]
    exact core.2.2.2 _ 0 (hessian_receiver_is_c2_lorentz H) a b
  simpa only [metricHessianResponseAt_origin] using
    hessian_response_unique_normal_form (metricHessianResponseAt E 0)
      (metric_response_hessian_affine_from_first_response E core.2.2.1) hs
      (regular_lorentz_hessian_covariance E core.1 core.2.1)
      (regular_lorentz_hessian_gauge E core.1 core.2.1)

theorem regular_lorentz_c2_normalized_exhaustion (E : MetricFieldResponse)
    (core : RegularLorentzResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ g : MetricField, ∀ germ : C2NormalizedMetricGerm g,
      E g 0 = coefficients.1 • ricciResponse (c2NormalizedLeviCivitaCurvature g germ) +
        coefficients.2.1 • scalarMetricResponse (c2NormalizedLeviCivitaCurvature g germ) +
          coefficients.2.2 • metric := by
  obtain ⟨coeff,h,unique⟩ := regular_lorentz_response_jet_exhaustion E core
  refine ⟨coeff,?_,?_⟩
  · intro g germ
    rw [core.2.1 g _ 0 (c2_normalized_is_lorentz g germ)
      (hessian_receiver_is_c2_lorentz _) (c2_normalized_metric_matches_receiver g germ),
      c2_normalizedLeviCivitaCurvature_eq_jet]
    exact h (c2MetricHessian g 0 germ.1 germ.2.1)
  · intro other ho
    apply unique other
    intro H
    have hh := ho (hessianMetricPolynomial H) (hessianMetricPolynomial_c2_normalized H)
    simpa only [c2_normalizedLeviCivitaCurvature_eq_jet,c2NormalizedMetricJetCurvature_receiver] using hh

theorem regular_lorentz_coordinate_response_normal_form (E : MetricFieldResponse)
    (core : RegularLorentzResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
        (frame : LorentzFrameAt g p B),
      E g p = coefficients.1 • coordinateRicci g p +
        coefficients.2.1 • coordinateScalarMetric g p + coefficients.2.2 • g p := by
  have hh : ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
        (frame : LorentzFrameAt g p B),
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
        coefficients.1 • ricciResponse (framedActualConnectionCurvature g p B symmetric regular frame) +
          coefficients.2.1 • scalarMetricResponse (framedActualConnectionCurvature g p B symmetric regular frame) +
            coefficients.2.2 • metric := by
    obtain ⟨coeff,h,unique⟩ := regular_lorentz_c2_normalized_exhaustion E core
    refine ⟨coeff,?_,?_⟩
    · intro g p B hs hr hf
      have hc := h (pointNormalizedMetric g p B) (c2_pointNormalizedMetric_germ g p B hs hr hf)
      have hn := core.1 (pointNormalChartMap g p B) 0 B (pointNormalChartMap_analytic g p B).contDiffAt
        (pointNormalChartMap_hasFDerivAt g p B hs) g
      have hdom : C2LorentzMetricAt g (pointNormalChartMap g p B 0) := by
        simpa only [pointNormalChartMap_zero] using (show C2LorentzMetricAt g p from ⟨hs,hr,B,hf⟩)
      specialize hn hdom
      simp only [pointNormalChartMap_pullback,pointNormalChartMap_zero,
        pointNormalChartMap_jacobian g p B hs] at hn
      rw [framedActualConnectionCurvature_eq_normal_chart]
      exact hn.symm.trans hc
    · intro other ho
      apply unique other
      intro g germ
      have he := ho g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) germ.1 germ.2.1
        (c2_normalizedMetric_identity_frame g germ)
      simpa only [coordinateFrameMatrix_refl,Matrix.transpose_one,one_mul,mul_one,
        framedActualConnectionCurvature_eq_normal_chart,c2_normalChartCurvature_retraction g germ] using he
  simpa only [actual_coordinate_response_identity_iff] using hh

#print axioms c2_normalized_is_lorentz
#print axioms hessian_receiver_is_c2_lorentz
#print axioms c2_lorentz_of_normal_value
#print axioms regular_lorentz_hessian_gauge
#print axioms regular_lorentz_hessian_covariance
#print axioms regular_lorentz_response_jet_exhaustion
#print axioms regular_lorentz_c2_normalized_exhaustion
#print axioms regular_lorentz_coordinate_response_normal_form
end
end AASCSemanticExhaustion
