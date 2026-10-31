import NormalMetricVolumeDensity
import ScalarFieldSourceCalculus

/-! Actual normal-point conversion of a covariant source tensor to its raised
tensor density and of the classical density current back to covariant divergence.
This is a finite-regularity local identification, not manifold/source gluing. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

def raisedSourceTensorDensity (g T : MetricField) : MetricField := fun p a b =>
  coordinateVolumeDensity g p *
    ∑ i : Fin 4, ∑ j : Fin 4, (g p)⁻¹ a i * (g p)⁻¹ b j * T p i j

def classicalTensorDensityCurrent (g t : MetricField) (p : CoordinatePoint) (e : Fin 4) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    (scalarPartial (fun x => t x a b * g x b e) p a - t p a b * lowerChristoffel g p b a e)

theorem canonical_metric_raised_two_diagonal (M : Tensor2) (a b : Fin 4) :
    (∑ i : Fin 4, ∑ j : Fin 4, metric a i * metric b j * M i j) = metric a a * metric b b * M a b := by
  simp [metric, Matrix.diagonal_apply, ite_mul, mul_ite]

theorem c2_normal_raised_density_hasFDerivAt (g T : MetricField) (germ : C2NormalizedMetricGerm g)
    (hT : ∀ i j, DifferentiableAt ℝ (fun x => T x i j) 0) (a b : Fin 4) :
    HasFDerivAt (fun x => raisedSourceTensorDensity g T x a b)
      (fderiv ℝ (fun x => raisedSourceTensorDensity g T x a b) 0) 0 := by
  apply DifferentiableAt.hasFDerivAt
  exact (c2_normal_metric_volume_hasFDerivAt_zero g germ).differentiableAt.mul
    (DifferentiableAt.fun_sum (fun i _ => DifferentiableAt.fun_sum (fun j _ =>
      (((c2_normal_metric_inverse_hasFDerivAt_zero g germ a i).differentiableAt.mul
        (c2_normal_metric_inverse_hasFDerivAt_zero g germ b j).differentiableAt).mul (hT i j)))))

theorem c2_normal_raised_density_partial (g T : MetricField) (germ : C2NormalizedMetricGerm g)
    (hT : ∀ i j, DifferentiableAt ℝ (fun x => T x i j) 0) (a b c : Fin 4) :
    scalarPartial (fun x => raisedSourceTensorDensity g T x a b) 0 c =
      metric a a * metric b b * scalarPartial (fun x => T x a b) 0 c := by
  have hd := ((c2_normal_metric_volume_hasFDerivAt_zero g germ).mul
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
        (((c2_normal_metric_inverse_hasFDerivAt_zero g germ a i).mul
          (c2_normal_metric_inverse_hasFDerivAt_zero g germ b j)).mul (hT i j).hasFDerivAt))))).fderiv
  change fderiv ℝ (fun x => raisedSourceTensorDensity g T x a b) 0 = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply, mul_zero,
    zero_mul, add_zero, zero_add, Pi.mul_apply, c2_normal_metric_volume_value g germ,
    one_mul, germ.2.2.1, canonical_metric_inverse]
  exact canonical_metric_raised_two_diagonal _ a b

theorem c2_normal_classical_density_current (g t : MetricField) (germ : C2NormalizedMetricGerm g)
    (ht : ∀ a b, DifferentiableAt ℝ (fun x => t x a b) 0) (e : Fin 4) :
    classicalTensorDensityCurrent g t 0 e =
      ∑ a : Fin 4, ∑ b : Fin 4, metric b e * scalarPartial (fun x => t x a b) 0 a := by
  unfold classicalTensorDensityCurrent
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [scalar_partial_mul_at_zero (fun x => t x a b) (fun x => g x b e)
    (ht a b) ((germ.2.1 b e).differentiableAt (by norm_num)) a]
  simp only [scalarPartial, lowerChristoffel, metricPartial, germ.2.2.2,
    ContinuousLinearMap.zero_apply, germ.2.2.1]
  ring

theorem c2_normal_density_current_eq_covariant_divergence (g T : MetricField)
    (germ : C2NormalizedMetricGerm g) (hT : ∀ a b, DifferentiableAt ℝ (fun x => T x a b) 0)
    (e : Fin 4) :
    classicalTensorDensityCurrent g (raisedSourceTensorDensity g T) 0 e = coordinateDivergence g T 0 e := by
  rw [c2_normal_classical_density_current g _ germ
    (fun a b => (c2_normal_raised_density_hasFDerivAt g T germ hT a b).differentiableAt),
    c2_normal_coordinateDivergence g germ]
  simp_rw [c2_normal_raised_density_partial g T germ hT]
  apply Finset.sum_congr rfl
  intro a _
  have delta (b : Fin 4) : metric b e * metric b b = if b = e then 1 else 0 := by
    fin_cases b <;> fin_cases e <;> norm_num [metric, Matrix.diagonal_apply]
  have factor (b : Fin 4) : metric b e * (metric a a * metric b b * scalarPartial (fun x => T x a b) 0 a) =
      (metric b e * metric b b) * (metric a a * scalarPartial (fun x => T x a b) 0 a) := by ring
  simp_rw [factor, delta, ite_mul, one_mul, zero_mul]
  simp

#print axioms canonical_metric_raised_two_diagonal
#print axioms c2_normal_raised_density_hasFDerivAt
#print axioms c2_normal_raised_density_partial
#print axioms c2_normal_classical_density_current
#print axioms c2_normal_density_current_eq_covariant_divergence
end
end AASCSemanticExhaustion
