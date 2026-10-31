import C2GeneralConnectionDerivative

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem c2_lowerChristoffel_curl (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p) (a b c d : Fin 4) :
    metricLowerChristoffelDerivative g p a d b (Pi.single c 1) -
      metricLowerChristoffelDerivative g p a c b (Pi.single d 1) =
        curvatureOfNormalHessian (c2MetricHessian g p symmetric regular) a b c d := by
  rw [metric_lowerChristoffel_derivative_basis, metric_lowerChristoffel_derivative_basis]
  let H := c2MetricHessian g p symmetric regular
  change (1 / 2 : ℝ) * ((H : Tensor4) a b d c + (H : Tensor4) a d b c - (H : Tensor4) d b a c) -
    (1 / 2 : ℝ) * ((H : Tensor4) a b c d + (H : Tensor4) a c b d - (H : Tensor4) c b a d) =
      curvatureOfNormalHessian H a b c d
  unfold curvatureOfNormalHessian
  rw [H.property.2 a b d c, H.property.1 d b a c, H.property.1 c b a d]
  ring

/-- The complete pre-cancellation curvature formula at an arbitrary point. -/
theorem c2_lowered_curvature_with_derivative_corrections (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) (a b c d : Fin 4) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) p a b c d =
      curvatureOfNormalHessian (c2MetricHessian g p symmetric regular) a b c d -
        (∑ e : Fin 4, metricPartial g p a e c * leviCivitaCoefficients g p e d b) +
        (∑ e : Fin 4, metricPartial g p a e d * leviCivitaCoefficients g p e c b) +
        (∑ e : Fin 4, g p a e * (∑ f : Fin 4,
          leviCivitaCoefficients g p e c f * leviCivitaCoefficients g p f d b)) -
        (∑ e : Fin 4, g p a e * (∑ f : Fin 4,
          leviCivitaCoefficients g p e d f * leviCivitaCoefficients g p f c b)) := by
  unfold loweredConnectionCurvature connectionCurvature
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [c2_differentiated_leviCivita_lowering g p regular nondegenerate a d b (Pi.single c 1),
    c2_differentiated_leviCivita_lowering g p regular nondegenerate a c b (Pi.single d 1)]
  have h := c2_lowerChristoffel_curl g p symmetric regular a b c d
  change metricLowerChristoffelDerivative g p a d b (Pi.single c 1) -
    metricLowerChristoffelDerivative g p a c b (Pi.single d 1) = _ at h
  simp only [metricPartial]
  linear_combination h

theorem compatible_metric_partial_connection_product (g : MetricField)
    (Γ : ConnectionCoefficients) (p : CoordinatePoint)
    (compatible : CoordinateMetricCompatible g Γ p) (a b c d : Fin 4) :
    (∑ e : Fin 4, metricPartial g p a e c * Γ p e d b) =
      (∑ k : Fin 4, Γ p k c a * lowerConnection g Γ p k d b) +
        (∑ k : Fin 4, g p a k * (∑ e : Fin 4, Γ p k c e * Γ p e d b)) := by
  have hfirst : (∑ e : Fin 4, ∑ k : Fin 4, Γ p k c a * g p k e * Γ p e d b) =
      ∑ k : Fin 4, Γ p k c a * lowerConnection g Γ p k d b := by
    unfold lowerConnection
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro e _
    ring
  have hsecond : (∑ e : Fin 4, ∑ k : Fin 4, Γ p k c e * g p a k * Γ p e d b) =
      ∑ k : Fin 4, g p a k * (∑ e : Fin 4, Γ p k c e * Γ p e d b) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp_rw [compatible a _ c]
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hfirst, hsecond]

/-- Actual general-coordinate curvature equals the Hessian expression plus
the two quadratic connection corrections. No normal-coordinate premise occurs. -/
theorem c2_general_coordinate_curvature_formula (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) (a b c d : Fin 4) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) p a b c d =
      curvatureOfNormalHessian (c2MetricHessian g p symmetric regular) a b c d +
        (∑ k : Fin 4, leviCivitaCoefficients g p k a d * lowerChristoffel g p k b c) -
        (∑ k : Fin 4, leviCivitaCoefficients g p k a c * lowerChristoffel g p k b d) := by
  rw [c2_lowered_curvature_with_derivative_corrections g p symmetric regular nondegenerate]
  have hc := leviCivita_metric_compatible g symmetric p nondegenerate
  rw [compatible_metric_partial_connection_product g (leviCivitaCoefficients g) p hc a b c d,
    compatible_metric_partial_connection_product g (leviCivitaCoefficients g) p hc a b d c]
  have hl (k u v : Fin 4) : lowerConnection g (leviCivitaCoefficients g) p k u v =
      lowerChristoffel g p k u v := leviCivita_lowering g p nondegenerate k u v
  simp_rw [hl, leviCivita_torsion_free g symmetric p _ d a,
    leviCivita_torsion_free g symmetric p _ c a,
    lowerChristoffel_torsion_free g symmetric p _ c b,
    lowerChristoffel_torsion_free g symmetric p _ d b]
  ring

#print axioms c2_lowerChristoffel_curl
#print axioms c2_lowered_curvature_with_derivative_corrections
#print axioms compatible_metric_partial_connection_product
#print axioms c2_general_coordinate_curvature_formula
end
end AASCSemanticExhaustion
