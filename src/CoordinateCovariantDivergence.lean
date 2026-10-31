import CoordinateRicciDerivative
import ContractedBianchiAlgebra
import ActualCurvatureAlgebraicLaws

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

def coordinateCovariantTensorDerivative (Γ : ConnectionCoefficients) (T : MetricField)
    (p : CoordinatePoint) (c a b : Fin 4) : ℝ :=
  scalarPartial (fun x => T x a b) p c - (∑ e : Fin 4, Γ p e c a * T p e b) -
    (∑ e : Fin 4, Γ p e c b * T p a e)

def coordinateDivergence (g T : MetricField) (p : CoordinatePoint) (b : Fin 4) : ℝ :=
  ∑ a : Fin 4, ∑ c : Fin 4, (g p)⁻¹ a c *
    coordinateCovariantTensorDerivative (leviCivitaCoefficients g) T p c a b

theorem c2_normal_coordinateDivergence (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (T : MetricField) (b : Fin 4) : coordinateDivergence g T 0 b =
      ∑ a : Fin 4, metric a a * scalarPartial (fun x => T x a b) 0 a := by
  simp only [coordinateDivergence, coordinateCovariantTensorDerivative,
    c2_normalized_metric_christoffel_zero g germ, zero_mul, Finset.sum_const_zero,
    sub_zero, germ.2.2.1, canonical_metric_inverse]
  exact canonical_metric_contraction_diagonal _

theorem coordinate_metric_covariant_derivative_zero (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (nondegenerate : (g p).det ≠ 0) (c a b : Fin 4) :
    coordinateCovariantTensorDerivative (leviCivitaCoefficients g) g p c a b = 0 := by
  have hc := leviCivita_metric_compatible g symmetric p nondegenerate a b c
  unfold coordinateCovariantTensorDerivative
  change metricPartial g p a b c - _ - _ = 0
  rw [hc]
  ring

theorem coordinate_metric_divergence_zero (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (nondegenerate : (g p).det ≠ 0) :
    ∀ b, coordinateDivergence g g p b = 0 := by
  intro b
  simp only [coordinateDivergence, coordinate_metric_covariant_derivative_zero g p symmetric nondegenerate,
    mul_zero, Finset.sum_const_zero]

theorem c3_normal_coordinate_contracted_bianchi_partial (g : MetricField)
    (germ : C3NormalizedMetricGerm g) (b : Fin 4) :
    (∑ a : Fin 4, metric a a * scalarPartial (fun x => coordinateRicci g x a b) 0 a) =
      (1 / 2 : ℝ) * scalarPartial (coordinateScalarCurvature g) 0 b := by
  simp_rw [c3_normal_coordinateRicci_partial_diagonal g germ]
  rw [c3_normal_coordinateScalar_partial_diagonal g germ]
  simp only [Finset.mul_sum, mul_assoc]
  simpa only [Finset.mul_sum, mul_assoc] using (contracted_bianchi_algebra (fun a => metric a a)
    (fun e a b c d => scalarPartial
      (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d) 0 e)
    (fun e a b c d => c3_normal_curvature_partial_skew_first g germ a b c d e)
    (fun e a b c d => c3_normal_curvature_partial_skew_last g germ a b c d e)
    (fun a b c d e => c3_normal_metric_differential_bianchi g germ a b c d e) b)

theorem c3_normal_coordinate_contracted_bianchi (g : MetricField)
    (germ : C3NormalizedMetricGerm g) (b : Fin 4) :
    coordinateDivergence g (coordinateRicci g) 0 b =
      (1 / 2 : ℝ) * scalarPartial (coordinateScalarCurvature g) 0 b := by
  rw [c2_normal_coordinateDivergence g (c3_normalized_metric_c2 g germ)]
  exact c3_normal_coordinate_contracted_bianchi_partial g germ b

theorem c3_normal_scalar_metric_divergence (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (b : Fin 4) : coordinateDivergence g (coordinateScalarMetric g) 0 b =
      scalarPartial (coordinateScalarCurvature g) 0 b := by
  rw [c2_normal_coordinateDivergence g (c3_normalized_metric_c2 g germ)]
  have hpartial (a c : Fin 4) : scalarPartial (fun x => coordinateScalarMetric g x a b) 0 c =
      metric a b * scalarPartial (coordinateScalarCurvature g) 0 c := by
    have hd := (c3_normal_coordinateScalar_hasFDerivAt g germ).mul
      ((germ.2.1 a b).differentiableAt (by norm_num)).hasFDerivAt
    have he := hd.fderiv
    change fderiv ℝ (fun x => coordinateScalarMetric g x a b) 0 = _ at he
    simp only [scalarPartial, he, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, germ.2.2.2, ContinuousLinearMap.zero_apply, mul_zero, zero_add, germ.2.2.1]
    rw [(c3_normal_coordinateScalar_hasFDerivAt g germ).fderiv]
  simp_rw [hpartial]
  have h := canonical_metric_double_contraction
    (fun c => scalarPartial (coordinateScalarCurvature g) 0 c) b
  have hs (a : Fin 4) : metric a a * metric a b = (if a = b then 1 else 0) := by
    fin_cases a <;> fin_cases b <;> norm_num [metric, Matrix.diagonal_apply]
  simp_rw [← mul_assoc, hs, ite_mul, one_mul, zero_mul]
  simp

#print axioms c2_normal_coordinateDivergence
#print axioms coordinate_metric_covariant_derivative_zero
#print axioms coordinate_metric_divergence_zero
#print axioms c3_normal_coordinate_contracted_bianchi_partial
#print axioms c3_normal_coordinate_contracted_bianchi
#print axioms c3_normal_scalar_metric_divergence
end
end AASCSemanticExhaustion
