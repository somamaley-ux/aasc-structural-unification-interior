import CoordinateLeviCivita
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem normalMetric_det_differentiable (R : curvatureSpace) :
    Differentiable ℝ (fun x => (normalMetricPolynomial R x).det) := by
  simp only [Matrix.det_apply']
  unfold normalMetricPolynomial
  fun_prop

theorem normalMetric_adjugate_differentiable (R : curvatureSpace) (a b : Fin 4) :
    Differentiable ℝ (fun x => (normalMetricPolynomial R x).adjugate a b) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  intro x
  have hdj (j : Fin 4) : DifferentiableAt ℝ (fun y : CoordinatePoint =>
      if σ j = b then (Pi.single a (1 : ℝ) : Fin 4 → ℝ) j
      else normalMetricPolynomial R y (σ j) j) x := by
    by_cases h : σ j = b
    · simp only [h, ite_true]
      fun_prop
    · simp only [h, ite_false]
      exact (normalMetricPolynomial_smooth R (σ j) j).differentiable (by simp) x
  exact (HasFDerivAt.finset_prod (u := Finset.univ) (fun j _ => (hdj j).hasFDerivAt)).differentiableAt

theorem normalMetric_inverse_differentiableAt (R : curvatureSpace) (x : CoordinatePoint)
    (nondegenerate : (normalMetricPolynomial R x).det ≠ 0) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => (normalMetricPolynomial R y)⁻¹ a b) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((normalMetric_det_differentiable R x).inv nondegenerate).mul
    (normalMetric_adjugate_differentiable R a b x)

theorem normalMetric_inverse_differentiableAt_zero (R : curvatureSpace) (a b : Fin 4) :
    DifferentiableAt ℝ (fun y => (normalMetricPolynomial R y)⁻¹ a b) 0 := by
  apply normalMetric_inverse_differentiableAt R 0 _ a b
  rw [normalMetricPolynomial_at_zero, canonical_lorentz_metric_det]
  norm_num

#print axioms normalMetric_det_differentiable
#print axioms normalMetric_adjugate_differentiable
#print axioms normalMetric_inverse_differentiableAt
#print axioms normalMetric_inverse_differentiableAt_zero
end
end AASCSemanticExhaustion
