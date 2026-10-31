import C2MetricInverseAt

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem c2_metric_lowerChristoffel_hasFDerivAt (g : MetricField) (p : CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (a b c : Fin 4) :
    HasFDerivAt (fun x => lowerChristoffel g x a b c)
      (metricLowerChristoffelDerivative g p a b c) p := by
  have hd := (((c2_metric_partial_differentiableAt g p smooth a c b).hasFDerivAt.add
    (c2_metric_partial_differentiableAt g p smooth a b c).hasFDerivAt).sub
      (c2_metric_partial_differentiableAt g p smooth b c a).hasFDerivAt).const_mul (1 / 2 : ℝ)
  simpa only [lowerChristoffel, metricLowerChristoffelDerivative, Pi.add_apply, Pi.sub_apply] using hd

theorem c2_normalized_metric_lowerChristoffel_zero (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (a b c : Fin 4) : lowerChristoffel g 0 a b c = 0 := by
  simp [lowerChristoffel, metricPartial, germ.2.2.2]

theorem c2_normalized_metric_christoffel_zero (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (a b c : Fin 4) :
    leviCivitaCoefficients g 0 a b c = 0 := by
  simp [leviCivitaCoefficients, c2_normalized_metric_lowerChristoffel_zero g germ]

theorem c2_normalized_metric_christoffel_hasFDerivAt (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (a b c : Fin 4) :
    HasFDerivAt (fun x => leviCivitaCoefficients g x a b c)
      (normalizedMetricChristoffelDerivative g a b c) 0 := by
  have hn : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hd (e : Fin 4) := (c2_metric_inverse_differentiableAt g 0 germ.2.1 hn a e).hasFDerivAt.mul
    (c2_metric_lowerChristoffel_hasFDerivAt g 0 germ.2.1 e b c)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun e _ => hd e)
  simpa only [leviCivitaCoefficients, normalizedMetricChristoffelDerivative, Pi.mul_apply,
    c2_normalized_metric_lowerChristoffel_zero g germ, zero_smul, add_zero, germ.2.2.1,
    canonical_metric_inverse] using hs

theorem c2_normalized_metric_christoffel_fderiv (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (a b c : Fin 4) :
    fderiv ℝ (fun x => leviCivitaCoefficients g x a b c) 0 =
      normalizedMetricChristoffelDerivative g a b c :=
  (c2_normalized_metric_christoffel_hasFDerivAt g germ a b c).fderiv

theorem c2_normalized_metric_leviCivita_curvature (g : MetricField)
    (germ : C2NormalizedMetricGerm g) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) 0 =
      ((c2NormalizedMetricJetCurvature g germ : curvatureSpace) : Tensor4) := by
  funext a b c d
  simp only [loweredConnectionCurvature, connectionCurvature,
    c2_normalized_metric_christoffel_zero g germ, zero_mul, Finset.sum_const_zero,
    add_zero, sub_zero, germ.2.2.1, c2_normalized_metric_christoffel_fderiv g germ,
    mul_sub, Finset.sum_sub_distrib]
  rw [normalized_metric_christoffel_derivative_lowering,
    normalized_metric_christoffel_derivative_lowering,
    metric_lowerChristoffel_derivative_basis, metric_lowerChristoffel_derivative_basis]
  let H := c2MetricHessian g 0 germ.1 germ.2.1
  change (1 / 2 : ℝ) * ((H : Tensor4) a b d c + (H : Tensor4) a d b c - (H : Tensor4) d b a c) -
    (1 / 2 : ℝ) * ((H : Tensor4) a b c d + (H : Tensor4) a c b d - (H : Tensor4) c b a d) =
      curvatureOfNormalHessian H a b c d
  unfold curvatureOfNormalHessian
  rw [H.property.2 a b d c, H.property.1 d b a c, H.property.1 c b a d]
  ring

def c2NormalizedLeviCivitaCurvature (g : MetricField) (germ : C2NormalizedMetricGerm g) : curvatureSpace :=
  ⟨loweredConnectionCurvature g (leviCivitaCoefficients g) 0, by
    rw [c2_normalized_metric_leviCivita_curvature g germ]
    exact (c2NormalizedMetricJetCurvature g germ).property⟩

theorem c2_normalizedLeviCivitaCurvature_eq_jet (g : MetricField) (germ : C2NormalizedMetricGerm g) :
    c2NormalizedLeviCivitaCurvature g germ = c2NormalizedMetricJetCurvature g germ :=
  Subtype.ext (c2_normalized_metric_leviCivita_curvature g germ)

theorem c2_actual_normalized_metric_response_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ g : MetricField, ∀ germ : C2NormalizedMetricGerm g,
      E g 0 = coefficients.1 • ricciResponse (c2NormalizedLeviCivitaCurvature g germ) +
        coefficients.2.1 • scalarMetricResponse (c2NormalizedLeviCivitaCurvature g germ) +
          coefficients.2.2 • metric := by
  simpa only [c2_normalizedLeviCivitaCurvature_eq_jet] using
    metric_response_c2_normalized_germ_exhaustion E core

#print axioms c2_metric_lowerChristoffel_hasFDerivAt
#print axioms c2_normalized_metric_lowerChristoffel_zero
#print axioms c2_normalized_metric_christoffel_zero
#print axioms c2_normalized_metric_christoffel_hasFDerivAt
#print axioms c2_normalized_metric_christoffel_fderiv
#print axioms c2_normalized_metric_leviCivita_curvature
#print axioms c2_normalizedLeviCivitaCurvature_eq_jet
#print axioms c2_actual_normalized_metric_response_exhaustion
end
end AASCSemanticExhaustion
