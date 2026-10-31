import CubicMetricPullbackJet
import NormalLeviCivitaCurvature
import MetricResponseTranslationConstancy

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def raisedCubicCoordinate (T : Tensor4) (i b c d : Fin 4) : ℝ :=
  ∑ e : Fin 4, metric i e * T e b c d

theorem raisedCubicCoordinate_laws (T : Tensor4) (laws : CubicCoordinateLaws T) :
    CubicCoordinateLaws (raisedCubicCoordinate T) := by
  constructor
  · intro i b c d
    unfold raisedCubicCoordinate
    simp_rw [laws.1 _ b c d]
  · intro i b c d
    unfold raisedCubicCoordinate
    simp_rw [laws.2 _ b c d]

theorem raisedCubicCoordinate_lower (T : Tensor4) (a b c d : Fin 4) :
    (∑ i : Fin 4, metric a i * raisedCubicCoordinate T i b c d) = T a b c d :=
  canonical_metric_double_contraction (fun e => T e b c d) a

theorem raisedCubicCoordinate_lower_right (T : Tensor4) (a b c d : Fin 4) :
    (∑ i : Fin 4, metric i b * raisedCubicCoordinate T i a c d) = T b a c d := by
  have hs (i : Fin 4) : metric i b = metric b i := by
    by_cases h : i = b
    · subst b; rfl
    · simp [metric, h, Ne.symm h]
  simp_rw [hs]
  exact raisedCubicCoordinate_lower T b a c d

theorem hessian_metric_scalarSecond (H : metricHessianSpace) (a b c d : Fin 4) :
    scalarSecondPartial (fun x => hessianMetricPolynomial H x a b) 0 c d =
      (H : Tensor4) a b c d := hessianMetricPolynomial_second H a b c d

theorem cubic_gauge_actual_twojet (H K : metricHessianSpace) (T : Tensor4)
    (laws : CubicCoordinateLaws T)
    (gauge : ∀ a b c d, (K : Tensor4) a b c d = T a b c d + T b a c d) :
    MetricTwoJetEqualAt
      (coordinateMetricPullback (hessianMetricPolynomial H) (cubicCoordinateMap (raisedCubicCoordinate T)))
      (hessianMetricPolynomial (H + K)) 0 := by
  have hl := raisedCubicCoordinate_laws T laws
  refine ⟨?_, ?_, ?_⟩
  · rw [cubic_metric_pullback_value _ _ hl, hessianMetricPolynomial_zero, hessianMetricPolynomial_zero]
  · intro a b
    rw [cubic_metric_pullback_first_zero _ (hessianMetricPolynomial_smooth H)
      (hessianMetricPolynomial_first_zero H) _ hl, hessianMetricPolynomial_first_zero]
  · intro a b c d
    rw [cubic_metric_pullback_second _ (hessianMetricPolynomial_smooth H)
      (hessianMetricPolynomial_zero H) (hessianMetricPolynomial_first_zero H) _ hl,
      hessian_metric_scalarSecond, hessian_metric_scalarSecond,
      raisedCubicCoordinate_lower, raisedCubicCoordinate_lower_right]
    change (H : Tensor4) a b c d + T a b c d + T b a c d =
      (H : Tensor4) a b c d + (K : Tensor4) a b c d
    rw [gauge]
    ring

/-- Cubic Hessian-gauge invariance is derived from naturality under an actual
local inverse chart and the original explicit two-jet order condition. -/
theorem metric_response_hessian_gauge_from_naturality (E : MetricFieldResponse)
    (natural : MetricResponseNatural E) (localOrder : MetricTwoJetLocal E) :
    HessianGaugeInvariant (metricHessianResponseAt E 0) := by
  intro H K hK
  obtain ⟨T, laws, gauge⟩ := hK
  have hjet := cubic_gauge_actual_twojet H K T laws gauge
  have heq := localOrder _ _ 0 hjet
  have hn := natural (cubicCoordinateMap (raisedCubicCoordinate T)) 0
    (cubicCoordinateMap_smoothCoordinateAt _) (hessianMetricPolynomial H)
  rw [cubic_coordinate_jacobian_zero _ (raisedCubicCoordinate_laws T laws),
    cubicCoordinateMap_zero] at hn
  simp only [Matrix.transpose_one, one_mul, mul_one] at hn
  rw [metricHessianResponseAt_origin, metricHessianResponseAt_origin]
  exact heq.symm.trans hn

#print axioms raisedCubicCoordinate_laws
#print axioms raisedCubicCoordinate_lower
#print axioms raisedCubicCoordinate_lower_right
#print axioms hessian_metric_scalarSecond
#print axioms cubic_gauge_actual_twojet
#print axioms metric_response_hessian_gauge_from_naturality
end
end AASCSemanticExhaustion
