import LorentzMetricPullbackJet
import CubicGaugeRealization

namespace AASCSemanticExhaustion
noncomputable section

theorem lorentz_frame_actual_twojet (L : LorentzComparison) (H K : metricHessianSpace)
    (transport : (K : Tensor4) = pullbackFour L.forward H) :
    MetricTwoJetEqualAt
      (coordinateMetricPullback (hessianMetricPolynomial H) (lorentzCoordinateMap L))
      (hessianMetricPolynomial K) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lorentz_metric_pullback_value, hessianMetricPolynomial_zero]
  · intro a b
    rw [lorentz_metric_pullback_first_zero, hessianMetricPolynomial_first_zero]
  · intro a b c d
    rw [lorentz_metric_pullback_second, hessian_metric_scalarSecond]
    exact (congrFun (congrFun (congrFun (congrFun transport a) b) c) d).symm

theorem metric_response_hessian_covariant_from_naturality (E : MetricFieldResponse)
    (natural : MetricResponseNatural E) (localOrder : MetricTwoJetLocal E) :
    HessianCovariant (metricHessianResponseAt E 0) := by
  intro L H K transport
  have heq := localOrder _ _ 0 (lorentz_frame_actual_twojet L H K transport)
  have hn := natural (lorentzCoordinateMap L) 0 (lorentzCoordinateMap_smoothCoordinateAt L 0)
    (hessianMetricPolynomial H)
  rw [lorentzCoordinateMap_jacobian, lorentzCoordinateMap_zero] at hn
  rw [metricHessianResponseAt_origin, metricHessianResponseAt_origin]
  exact heq.symm.trans hn

#print axioms lorentz_frame_actual_twojet
#print axioms metric_response_hessian_covariant_from_naturality
end
end AASCSemanticExhaustion
