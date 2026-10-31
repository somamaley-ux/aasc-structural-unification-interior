import LorentzCoordinateMaps
import ScalarSmoothJetRules

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem lorentzCoordinateEquiv_basis (L : LorentzComparison) (c i : Fin 4) :
    lorentzCoordinateEquiv L (Pi.single c 1) i = L.forward i c := by
  change L.forward.mulVec (Pi.single c 1) i = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, ite_mul, mul_ite]

theorem quadraticSecondDerivative_lorentz (Q : Tensor2) (symmetric : ∀ u v, Q u v = Q v u)
    (L : LorentzComparison) (c d : Fin 4) :
    quadraticSecondDerivative Q (lorentzCoordinateEquiv L (Pi.single c 1))
      (lorentzCoordinateEquiv L (Pi.single d 1)) =
        ∑ u : Fin 4, ∑ v : Fin 4, Q u v * L.forward u c * L.forward v d := by
  simp only [quadraticSecondDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
    coordinateProjection, ContinuousLinearMap.proj_apply, lorentzCoordinateEquiv_basis,
    mul_add, Finset.sum_add_distrib]
  have hsum : (∑ u : Fin 4, ∑ v : Fin 4, Q u v * (L.forward v c * L.forward u d)) =
      ∑ u : Fin 4, ∑ v : Fin 4, Q u v * (L.forward u c * L.forward v d) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [symmetric v u]
  rw [hsum]
  simp only [mul_assoc]
  ring

theorem hessian_metric_lorentz_composition_fderiv (H : metricHessianSpace) (L : LorentzComparison)
    (x : CoordinatePoint) (i j : Fin 4) :
    fderiv ℝ (fun y => hessianMetricPolynomial H (lorentzCoordinateMap L y) i j) x =
      (quadraticDerivative (hessianRow H i j) (lorentzCoordinateMap L x)).comp
        (lorentzCoordinateEquiv L).toContinuousLinearMap := by
  have hd := (hessianMetricPolynomial_hasFDerivAt H (lorentzCoordinateMap L x) i j).comp x
    (lorentzCoordinateMap_hasFDerivAt L x)
  change HasFDerivAt (fun y => hessianMetricPolynomial H (lorentzCoordinateMap L y) i j)
    ((quadraticDerivative (hessianRow H i j) (lorentzCoordinateMap L x)).comp
      (lorentzCoordinateEquiv L).toContinuousLinearMap) x at hd
  exact hd.fderiv

theorem hessian_metric_lorentz_composition_second (H : metricHessianSpace) (L : LorentzComparison)
    (i j c d : Fin 4) :
    scalarSecondPartial (fun x => hessianMetricPolynomial H (lorentzCoordinateMap L x) i j) 0 c d =
      ∑ u : Fin 4, ∑ v : Fin 4, (H : Tensor4) i j u v * L.forward u c * L.forward v d := by
  have hpartial : (fun x => scalarPartial
      (fun y => hessianMetricPolynomial H (lorentzCoordinateMap L y) i j) x c) =
        (quadraticSecondDerivative (hessianRow H i j)
          (lorentzCoordinateEquiv L (Pi.single c 1))).comp
            (lorentzCoordinateEquiv L).toContinuousLinearMap := by
    funext x
    unfold scalarPartial
    rw [hessian_metric_lorentz_composition_fderiv]
    change quadraticDerivative (hessianRow H i j) (lorentzCoordinateMap L x)
      (lorentzCoordinateEquiv L (Pi.single c 1)) = _
    exact congrFun (quadraticDerivative_eval_linear (hessianRow H i j)
      (lorentzCoordinateEquiv L (Pi.single c 1))) (lorentzCoordinateMap L x)
  unfold scalarSecondPartial
  rw [hpartial]
  unfold scalarPartial
  rw [(ContinuousLinearMap.hasFDerivAt _).fderiv]
  exact quadraticSecondDerivative_lorentz (hessianRow H i j) (H.property.2 i j) L c d

#print axioms lorentzCoordinateEquiv_basis
#print axioms quadraticSecondDerivative_lorentz
#print axioms hessian_metric_lorentz_composition_fderiv
#print axioms hessian_metric_lorentz_composition_second
end
end AASCSemanticExhaustion
