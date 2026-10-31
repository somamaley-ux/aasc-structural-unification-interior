import ActualMetricHessian
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem smooth_metric_det_differentiableAt (g : MetricField) (p : CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) :
    DifferentiableAt ℝ (fun x => (g x).det) p := by
  simp only [Matrix.det_apply']
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  exact (HasFDerivAt.finset_prod (u := Finset.univ)
    (fun j _ => ((smooth (σ j) j).differentiableAt (by simp)).hasFDerivAt)).differentiableAt

theorem smooth_metric_adjugate_differentiableAt (g : MetricField) (p : CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (a b : Fin 4) :
    DifferentiableAt ℝ (fun x => (g x).adjugate a b) p := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
  apply DifferentiableAt.fun_sum
  intro σ _
  apply DifferentiableAt.const_mul
  have hd (j : Fin 4) : DifferentiableAt ℝ (fun x : CoordinatePoint =>
      if σ j = b then (Pi.single a (1 : ℝ) : CoordinatePoint) j else g x (σ j) j) p := by
    by_cases h : σ j = b
    · simp only [h, ite_true]
      fun_prop
    · simp only [h, ite_false]
      exact (smooth (σ j) j).differentiableAt (by simp)
  exact (HasFDerivAt.finset_prod (u := Finset.univ) (fun j _ => (hd j).hasFDerivAt)).differentiableAt

theorem smooth_metric_inverse_differentiableAt (g : MetricField) (p : CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) (a b : Fin 4) :
    DifferentiableAt ℝ (fun x => (g x)⁻¹ a b) p := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((smooth_metric_det_differentiableAt g p smooth).inv nondegenerate).mul
    (smooth_metric_adjugate_differentiableAt g p smooth a b)

theorem smooth_metric_partial_differentiableAt (g : MetricField) (p : CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (a b c : Fin 4) :
    DifferentiableAt ℝ (fun x => metricPartial g x a b c) p := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ (fun x => g x a b)) p :=
    ((smooth a b).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hc : DifferentiableAt ℝ (fun _ : CoordinatePoint => (Pi.single c 1 : CoordinatePoint)) p :=
    differentiableAt_const _
  exact hdf.clm_apply hc

#print axioms smooth_metric_det_differentiableAt
#print axioms smooth_metric_adjugate_differentiableAt
#print axioms smooth_metric_inverse_differentiableAt
#print axioms smooth_metric_partial_differentiableAt
end
end AASCSemanticExhaustion
