import QuadraticMetricSecondJet
import QuadraticNormalCurvatureAlgebra

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

theorem c2_general_normalizing_metric_partial_zero (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (nondegenerate : (g 0).det ≠ 0)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateMetricPullback g (normalizingCoordinateMap g) x a b) 0 c = 0 := by
  have hc := leviCivita_metric_compatible g symmetric 0 nondegenerate a b c
  have h1 : (∑ i : Fin 4, g 0 i b * normalCoordinateCorrection g i a c) =
      -(∑ i : Fin 4, leviCivitaCoefficients g 0 i c a * g 0 i b) := by
    simp only [normalCoordinateCorrection, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [leviCivita_torsion_free g symmetric 0 i a c]
    ring
  have h2 : (∑ i : Fin 4, g 0 a i * normalCoordinateCorrection g i b c) =
      -(∑ i : Fin 4, leviCivitaCoefficients g 0 i c b * g 0 a i) := by
    simp only [normalCoordinateCorrection, mul_neg, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [leviCivita_torsion_free g symmetric 0 i b c]
    ring
  unfold normalizingCoordinateMap
  rw [c2_quadratic_identity_metric_pullback_partial g regular _
    (normalCoordinateCorrection_symmetric g symmetric) a b c, h1, h2, hc]
  ring

theorem c2_general_normalizing_metric_first_zero (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (nondegenerate : (g 0).det ≠ 0)
    (a b : Fin 4) :
    fderiv ℝ (fun x => coordinateMetricPullback g (normalizingCoordinateMap g) x a b) 0 = 0 := by
  apply continuousLinearMap_zero_of_coordinate_basis
  intro c
  exact c2_general_normalizing_metric_partial_zero g symmetric regular nondegenerate a b c

theorem c2_general_normalizing_metric_regular (g : MetricField)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) :
    ∀ a b, ContDiffAt ℝ 2 (fun x => coordinateMetricPullback g (normalizingCoordinateMap g) x a b) 0 := by
  apply c2_coordinateMetricPullback_contDiffAt g _ 0 (normalizingCoordinateMap_local_chart g).1
  simpa only [normalizingCoordinateMap_zero] using regular

theorem general_normalizing_metric_value (g : MetricField) (symmetric : MetricFieldSymmetric g) :
    coordinateMetricPullback g (normalizingCoordinateMap g) 0 = g 0 := by
  rw [coordinateMetricPullback_matrix, normalizingCoordinateMap_zero,
    normalizingCoordinateMap_jacobian g symmetric, Matrix.transpose_one, one_mul, mul_one]

theorem c2_first_flat_metric_curvature (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (nondegenerate : (g 0).det ≠ 0)
    (first : ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0) (a b c d : Fin 4) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) 0 a b c d =
      curvatureOfNormalHessian (c2MetricHessian g 0 symmetric regular) a b c d := by
  have hz (i u v : Fin 4) : leviCivitaCoefficients g 0 i u v = 0 := by
    simp [leviCivitaCoefficients, lowerChristoffel, metricPartial, first]
  rw [c2_general_coordinate_curvature_formula g 0 symmetric regular nondegenerate]
  simp only [hz, zero_mul, Finset.sum_const_zero, add_zero, sub_zero]

theorem c2_normalizing_metric_hessian (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) :
    ((c2MetricHessian (coordinateMetricPullback g (normalizingCoordinateMap g)) 0
      (coordinateMetricPullback_symmetric g symmetric _) (c2_general_normalizing_metric_regular g regular) :
        metricHessianSpace) : Tensor4) =
      (c2MetricHessian g 0 symmetric regular : Tensor4) +
        quadraticMetricJetCorrection (g 0) (fun a b c => metricPartial g 0 a b c) (normalCoordinateCorrection g) := by
  funext a b c d
  change scalarSecondPartial (fun x => coordinateMetricPullback g
    (quadraticIdentityMap (normalCoordinateCorrection g)) x a b) 0 c d =
      scalarSecondPartial (fun x => g x a b) 0 c d + _
  rw [c2_quadratic_identity_metric_second g regular _ (normalCoordinateCorrection_symmetric g symmetric)]
  unfold quadraticMetricJetCorrection
  ring

/-- Actual connection curvature is preserved by the constructed quadratic
normalizing chart, at every nondegenerate C² metric point with arbitrary metric
value and arbitrary first derivatives. All derivative corrections are proved. -/
theorem c2_normalizing_actual_curvature_preserved (g : MetricField) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0) (nondegenerate : (g 0).det ≠ 0) :
    loweredConnectionCurvature (coordinateMetricPullback g (normalizingCoordinateMap g))
      (leviCivitaCoefficients (coordinateMetricPullback g (normalizingCoordinateMap g))) 0 =
        loweredConnectionCurvature g (leviCivitaCoefficients g) 0 := by
  have hn : (coordinateMetricPullback g (normalizingCoordinateMap g) 0).det ≠ 0 := by
    rw [general_normalizing_metric_value g symmetric]
    exact nondegenerate
  funext a b c d
  rw [c2_first_flat_metric_curvature _ (coordinateMetricPullback_symmetric g symmetric _)
    (c2_general_normalizing_metric_regular g regular) hn
    (c2_general_normalizing_metric_first_zero g symmetric regular nondegenerate)]
  rw [c2_normalizing_metric_hessian g symmetric regular, curvatureOfNormalHessian_add]
  have hS : (fun a b c => metricPartial g 0 a b c) =
      compatibleMetricFirstJet (g 0) (fun i a b => leviCivitaCoefficients g 0 i a b) := by
    funext a b c
    exact leviCivita_metric_compatible g symmetric 0 nondegenerate a b c
  have hcorr := quadratic_normalizing_curvature_correction (g 0)
    (fun i a b => leviCivitaCoefficients g 0 i a b) (symmetric 0)
      (leviCivita_torsion_free g symmetric 0) a b c d
  rw [← hS] at hcorr
  change curvatureOfNormalHessian (quadraticMetricJetCorrection (g 0)
    (fun a b c => metricPartial g 0 a b c) (normalCoordinateCorrection g)) a b c d = _ at hcorr
  change curvatureOfNormalHessian (c2MetricHessian g 0 symmetric regular) a b c d +
    curvatureOfNormalHessian (quadraticMetricJetCorrection (g 0)
      (fun a b c => metricPartial g 0 a b c) (normalCoordinateCorrection g)) a b c d = _
  rw [hcorr]
  simp_rw [leviCivita_lowering g 0 nondegenerate]
  linarith [c2_general_coordinate_curvature_formula g 0 symmetric regular nondegenerate a b c d]

#print axioms c2_general_normalizing_metric_partial_zero
#print axioms c2_general_normalizing_metric_first_zero
#print axioms c2_general_normalizing_metric_regular
#print axioms general_normalizing_metric_value
#print axioms c2_first_flat_metric_curvature
#print axioms c2_normalizing_metric_hessian
#print axioms c2_normalizing_actual_curvature_preserved
end
end AASCSemanticExhaustion
