import MetricJetCurvatureRealization
import LorentzInvariantBaseline
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Instances.Matrix

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators Topology

/-- A concrete polynomial candidate metric from the constructed normal Hessian.
The smooth-neighborhood nondegeneracy/signature and actual curvature-jet
identifications are not encoded merely by naming this candidate a metric. -/
def normalMetricPolynomial (R : curvatureSpace) (x : Fin 4 → ℝ) : Tensor2 :=
  fun a b => metric a b + (1 / 2 : ℝ) *
    ∑ c : Fin 4, ∑ d : Fin 4, normalMetricHessian R a b c d * x c * x d

theorem normalMetricPolynomial_at_zero (R : curvatureSpace) :
    normalMetricPolynomial R 0 = metric := by
  ext a b
  simp [normalMetricPolynomial]

theorem normalMetricPolynomial_symmetric (R : curvatureSpace)
    (x : Fin 4 → ℝ) (a b : Fin 4) :
    normalMetricPolynomial R x a b = normalMetricPolynomial R x b a := by
  have hm : metric a b = metric b a := by
    by_cases h : a = b
    · subst b; rfl
    · simp [metric, h, Ne.symm h]
  unfold normalMetricPolynomial
  rw [hm]
  simp_rw [normalMetricHessian_metric_symmetry R a b]

theorem normalMetricPolynomial_smooth (R : curvatureSpace) (a b : Fin 4) :
    ContDiff ℝ ⊤ (fun x : Fin 4 → ℝ => normalMetricPolynomial R x a b) := by
  unfold normalMetricPolynomial
  fun_prop

theorem normalMetricPolynomial_continuous (R : curvatureSpace) :
    Continuous (normalMetricPolynomial R) :=
  continuous_pi fun a => continuous_pi fun b =>
    (normalMetricPolynomial_smooth R a b).continuous

theorem canonical_lorentz_metric_det : metric.det = -1 := by
  norm_num [metric, Matrix.det_diagonal, Fin.prod_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem normalMetricPolynomial_det_nonzero_near_zero (R : curvatureSpace) :
    ∀ᶠ x in 𝓝 (0 : Fin 4 → ℝ), (normalMetricPolynomial R x).det ≠ 0 := by
  apply ((normalMetricPolynomial_continuous R).matrix_det.continuousAt).eventually_ne
  rw [normalMetricPolynomial_at_zero, canonical_lorentz_metric_det]
  norm_num

theorem normalMetricPolynomial_nondegenerate_neighborhood (R : curvatureSpace) :
    ∃ U : Set (Fin 4 → ℝ), IsOpen U ∧ 0 ∈ U ∧
      ∀ x ∈ U, (normalMetricPolynomial R x).det ≠ 0 := by
  obtain ⟨U, hsub, hopen, hzero⟩ :=
    mem_nhds_iff.mp (normalMetricPolynomial_det_nonzero_near_zero R)
  exact ⟨U, hopen, hzero, fun x hx => hsub hx⟩

#print axioms normalMetricPolynomial_at_zero
#print axioms normalMetricPolynomial_symmetric
#print axioms normalMetricPolynomial_smooth
#print axioms normalMetricPolynomial_continuous
#print axioms canonical_lorentz_metric_det
#print axioms normalMetricPolynomial_det_nonzero_near_zero
#print axioms normalMetricPolynomial_nondegenerate_neighborhood
end
end AASCSemanticExhaustion
