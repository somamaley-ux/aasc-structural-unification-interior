import SmoothMetricInverseAt
import NormalLeviCivitaCurvature
import GeometricMetricResponseExhaustion

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def metricLowerChristoffelDerivative (g : MetricField) (p : CoordinatePoint) (a b c : Fin 4) :
    CoordinatePoint →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (fderiv ℝ (fun x => metricPartial g x a c b) p +
    fderiv ℝ (fun x => metricPartial g x a b c) p -
      fderiv ℝ (fun x => metricPartial g x b c a) p)

theorem metric_lowerChristoffel_hasFDerivAt (g : MetricField) (p : CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (a b c : Fin 4) :
    HasFDerivAt (fun x => lowerChristoffel g x a b c)
      (metricLowerChristoffelDerivative g p a b c) p := by
  have hd := (((smooth_metric_partial_differentiableAt g p smooth a c b).hasFDerivAt.add
    (smooth_metric_partial_differentiableAt g p smooth a b c).hasFDerivAt).sub
      (smooth_metric_partial_differentiableAt g p smooth b c a).hasFDerivAt).const_mul (1 / 2 : ℝ)
  simpa only [lowerChristoffel, metricLowerChristoffelDerivative, Pi.add_apply, Pi.sub_apply] using hd

theorem normalized_metric_lowerChristoffel_zero (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (a b c : Fin 4) : lowerChristoffel g 0 a b c = 0 := by
  simp [lowerChristoffel, metricPartial, germ.2.2.2]

theorem metric_lowerChristoffel_derivative_basis (g : MetricField) (p : CoordinatePoint)
    (a b c d : Fin 4) :
    metricLowerChristoffelDerivative g p a b c (Pi.single d 1) =
      (1 / 2 : ℝ) * (scalarSecondPartial (fun x => g x a c) p b d +
        scalarSecondPartial (fun x => g x a b) p c d - scalarSecondPartial (fun x => g x b c) p a d) := by
  simp only [metricLowerChristoffelDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  rfl

def normalizedMetricChristoffelDerivative (g : MetricField) (a b c : Fin 4) : CoordinatePoint →L[ℝ] ℝ :=
  ∑ e : Fin 4, metric a e • metricLowerChristoffelDerivative g 0 e b c

theorem normalized_metric_christoffel_zero (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (a b c : Fin 4) :
    leviCivitaCoefficients g 0 a b c = 0 := by
  simp [leviCivitaCoefficients, normalized_metric_lowerChristoffel_zero g germ]

theorem normalized_metric_christoffel_hasFDerivAt (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (a b c : Fin 4) :
    HasFDerivAt (fun x => leviCivitaCoefficients g x a b c)
      (normalizedMetricChristoffelDerivative g a b c) 0 := by
  have hn : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hd (e : Fin 4) := (smooth_metric_inverse_differentiableAt g 0 germ.2.1 hn a e).hasFDerivAt.mul
    (metric_lowerChristoffel_hasFDerivAt g 0 germ.2.1 e b c)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun e _ => hd e)
  simpa only [leviCivitaCoefficients, normalizedMetricChristoffelDerivative, Pi.mul_apply,
    normalized_metric_lowerChristoffel_zero g germ, zero_smul, add_zero, germ.2.2.1,
    canonical_metric_inverse] using hs

theorem normalized_metric_christoffel_fderiv (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (a b c : Fin 4) :
    fderiv ℝ (fun x => leviCivitaCoefficients g x a b c) 0 =
      normalizedMetricChristoffelDerivative g a b c :=
  (normalized_metric_christoffel_hasFDerivAt g germ a b c).fderiv

theorem normalized_metric_christoffel_derivative_lowering (g : MetricField)
    (a b c : Fin 4) (v : CoordinatePoint) :
    (∑ e : Fin 4, metric a e * normalizedMetricChristoffelDerivative g e b c v) =
      metricLowerChristoffelDerivative g 0 a b c v := by
  simpa [normalizedMetricChristoffelDerivative] using
    canonical_metric_double_contraction (fun f => metricLowerChristoffelDerivative g 0 f b c v) a

theorem normalized_metric_leviCivita_curvature (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) 0 =
      ((normalizedMetricJetCurvature g germ : curvatureSpace) : Tensor4) := by
  funext a b c d
  simp only [loweredConnectionCurvature, connectionCurvature,
    normalized_metric_christoffel_zero g germ, zero_mul, Finset.sum_const_zero,
    add_zero, sub_zero, germ.2.2.1, normalized_metric_christoffel_fderiv g germ,
    mul_sub, Finset.sum_sub_distrib]
  rw [normalized_metric_christoffel_derivative_lowering,
    normalized_metric_christoffel_derivative_lowering,
    metric_lowerChristoffel_derivative_basis, metric_lowerChristoffel_derivative_basis]
  let H := actualMetricHessian g 0 germ.1 germ.2.1
  change (1 / 2 : ℝ) * ((H : Tensor4) a b d c + (H : Tensor4) a d b c - (H : Tensor4) d b a c) -
    (1 / 2 : ℝ) * ((H : Tensor4) a b c d + (H : Tensor4) a c b d - (H : Tensor4) c b a d) =
      curvatureOfNormalHessian H a b c d
  unfold curvatureOfNormalHessian
  rw [H.property.2 a b d c, H.property.1 d b a c, H.property.1 c b a d]
  ring

def normalizedLeviCivitaCurvature (g : MetricField) (germ : NormalizedSmoothMetricGerm g) : curvatureSpace :=
  ⟨loweredConnectionCurvature g (leviCivitaCoefficients g) 0, by
    rw [normalized_metric_leviCivita_curvature g germ]
    exact (normalizedMetricJetCurvature g germ).property⟩

theorem normalizedLeviCivitaCurvature_eq_jet (g : MetricField) (germ : NormalizedSmoothMetricGerm g) :
    normalizedLeviCivitaCurvature g germ = normalizedMetricJetCurvature g germ :=
  Subtype.ext (normalized_metric_leviCivita_curvature g germ)

theorem actual_normalized_metric_response_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ, ∀ g : MetricField, ∀ germ : NormalizedSmoothMetricGerm g,
      E g 0 = coefficients.1 • ricciResponse (normalizedLeviCivitaCurvature g germ) +
        coefficients.2.1 • scalarMetricResponse (normalizedLeviCivitaCurvature g germ) +
          coefficients.2.2 • metric := by
  simpa only [normalizedLeviCivitaCurvature_eq_jet] using
    metric_field_response_normalized_germ_exhaustion E core

#print axioms metric_lowerChristoffel_hasFDerivAt
#print axioms normalized_metric_lowerChristoffel_zero
#print axioms metric_lowerChristoffel_derivative_basis
#print axioms normalized_metric_christoffel_zero
#print axioms normalized_metric_christoffel_hasFDerivAt
#print axioms normalized_metric_christoffel_fderiv
#print axioms normalized_metric_christoffel_derivative_lowering
#print axioms normalized_metric_leviCivita_curvature
#print axioms normalizedLeviCivitaCurvature_eq_jet
#print axioms actual_normalized_metric_response_exhaustion
end
end AASCSemanticExhaustion
