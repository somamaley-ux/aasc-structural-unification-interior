import NormalMetricInverseJet

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

def coordinateRicci (g : MetricField) (p : CoordinatePoint) : Tensor2 := fun a b =>
  ∑ i : Fin 4, ∑ j : Fin 4, (g p)⁻¹ i j * loweredConnectionCurvature g (leviCivitaCoefficients g) p i a j b

def coordinateScalarCurvature (g : MetricField) (p : CoordinatePoint) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, (g p)⁻¹ a b * coordinateRicci g p a b

def coordinateScalarMetric (g : MetricField) (p : CoordinatePoint) : Tensor2 :=
  coordinateScalarCurvature g p • g p

def normalRicciDerivative (g : MetricField) (a b : Fin 4) : CoordinatePoint →L[ℝ] ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, metric i j • normalCurvatureDerivative g i a j b

def normalScalarDerivative (g : MetricField) : CoordinatePoint →L[ℝ] ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, metric a b • normalRicciDerivative g a b

theorem c3_normal_coordinateRicci_hasFDerivAt (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (a b : Fin 4) : HasFDerivAt (fun x => coordinateRicci g x a b) (normalRicciDerivative g a b) 0 := by
  have germ2 := c3_normalized_metric_c2 g germ
  have hd (i j : Fin 4) := (c2_normal_metric_inverse_hasFDerivAt_zero g germ2 i j).mul
    (c3_normal_metric_curvature_hasFDerivAt g germ i a j b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd i j))
  simpa only [coordinateRicci, normalRicciDerivative, Pi.mul_apply, germ.2.2.1,
    canonical_metric_inverse, smul_zero, add_zero] using hs

theorem c3_normal_coordinateScalar_hasFDerivAt (g : MetricField) (germ : C3NormalizedMetricGerm g) :
    HasFDerivAt (coordinateScalarCurvature g) (normalScalarDerivative g) 0 := by
  have germ2 := c3_normalized_metric_c2 g germ
  have hd (a b : Fin 4) := (c2_normal_metric_inverse_hasFDerivAt_zero g germ2 a b).mul
    (c3_normal_coordinateRicci_hasFDerivAt g germ a b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => hd a b))
  simpa only [coordinateScalarCurvature, normalScalarDerivative, Pi.mul_apply, germ.2.2.1,
    canonical_metric_inverse, smul_zero, add_zero] using hs

theorem c3_normal_coordinateRicci_partial (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (a b c : Fin 4) :
    scalarPartial (fun x => coordinateRicci g x a b) 0 c =
      ∑ i : Fin 4, ∑ j : Fin 4, metric i j *
        scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x i a j b) 0 c := by
  have hd (i j : Fin 4) := (c3_normal_metric_curvature_hasFDerivAt g germ i a j b).fderiv
  simp only [scalarPartial, (c3_normal_coordinateRicci_hasFDerivAt g germ a b).fderiv,
    normalRicciDerivative, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hd]

theorem c3_normal_coordinateScalar_partial (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (c : Fin 4) : scalarPartial (coordinateScalarCurvature g) 0 c =
      ∑ a : Fin 4, ∑ b : Fin 4, metric a b * scalarPartial (fun x => coordinateRicci g x a b) 0 c := by
  have hd (a b : Fin 4) := (c3_normal_coordinateRicci_hasFDerivAt g germ a b).fderiv
  simp only [scalarPartial, (c3_normal_coordinateScalar_hasFDerivAt g germ).fderiv,
    normalScalarDerivative, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hd]

theorem canonical_metric_contraction_diagonal (U : Tensor2) :
    (∑ i : Fin 4, ∑ j : Fin 4, metric i j * U i j) = ∑ i : Fin 4, metric i i * U i i := by
  apply Finset.sum_congr rfl
  intro i _
  simp [metric, Matrix.diagonal_apply, ite_mul]

theorem c3_normal_coordinateRicci_partial_diagonal (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (a b c : Fin 4) : scalarPartial (fun x => coordinateRicci g x a b) 0 c =
      ∑ i : Fin 4, metric i i * scalarPartial
        (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x i a i b) 0 c := by
  rw [c3_normal_coordinateRicci_partial g germ]
  exact canonical_metric_contraction_diagonal _

theorem c3_normal_coordinateScalar_partial_diagonal (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (c : Fin 4) : scalarPartial (coordinateScalarCurvature g) 0 c =
      ∑ a : Fin 4, ∑ i : Fin 4, metric a a * metric i i * scalarPartial
        (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x i a i a) 0 c := by
  rw [c3_normal_coordinateScalar_partial g germ, canonical_metric_contraction_diagonal]
  simp_rw [c3_normal_coordinateRicci_partial_diagonal g germ]
  simp only [Finset.mul_sum, mul_assoc]

#print axioms c3_normal_coordinateRicci_hasFDerivAt
#print axioms c3_normal_coordinateScalar_hasFDerivAt
#print axioms c3_normal_coordinateRicci_partial
#print axioms c3_normal_coordinateScalar_partial
#print axioms canonical_metric_contraction_diagonal
#print axioms c3_normal_coordinateRicci_partial_diagonal
#print axioms c3_normal_coordinateScalar_partial_diagonal
end
end AASCSemanticExhaustion
