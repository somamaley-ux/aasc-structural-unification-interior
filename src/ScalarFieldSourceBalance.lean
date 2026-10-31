import ScalarFieldStressDerivative

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

def scalarFieldWaveOperator (g : MetricField) (φ : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  ∑ a : Fin 4, ∑ c : Fin 4, (g p)⁻¹ a c *
    (scalarSecondPartial φ p a c - ∑ e : Fin 4, leviCivitaCoefficients g p e c a * scalarPartial φ p e)

theorem scalar_source_balance_algebra (P : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ)
    (symmetric : ∀ a b, H a b = H b a) (u μ : ℝ) (b : Fin 4) :
    (∑ a : Fin 4, metric a a * (P a * H b a + P b * H a a -
      metric a b * ((∑ e : Fin 4, metric e e * P e * H e a) + μ * u * P a))) =
      ((∑ a : Fin 4, metric a a * H a a) - μ * u) * P b := by
  let Q := fun a => (∑ e : Fin 4, metric e e * P e * H e a) + μ * u * P a
  have delta (a : Fin 4) : metric a a * metric a b = if a = b then 1 else 0 := by
    fin_cases a <;> fin_cases b <;> norm_num [metric, Matrix.diagonal_apply]
  have baseline : (∑ a : Fin 4, metric a a * (metric a b * Q a)) = Q b := by
    simp_rw [← mul_assoc, delta, ite_mul, one_mul, zero_mul]
    simp
  have cross : (∑ a : Fin 4, metric a a * (P a * H b a)) =
      ∑ a : Fin 4, metric a a * P a * H a b := by
    apply Finset.sum_congr rfl
    intro a _
    rw [symmetric b a]
    ring
  have trace : (∑ a : Fin 4, metric a a * (P b * H a a)) =
      P b * ∑ a : Fin 4, metric a a * H a a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  change (∑ a : Fin 4, metric a a * (P a * H b a + P b * H a a - metric a b * Q a)) = _
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [baseline, cross, trace]
  dsimp [Q]
  ring

theorem c2_normal_scalar_wave_operator (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) : scalarFieldWaveOperator g φ 0 =
      ∑ a : Fin 4, metric a a * scalarSecondPartial φ 0 a a := by
  simp only [scalarFieldWaveOperator, c2_normalized_metric_christoffel_zero g germ,
    zero_mul, Finset.sum_const_zero, sub_zero, germ.2.2.1, canonical_metric_inverse]
  exact canonical_metric_contraction_diagonal _

/-- The source divergence is derived from the actual scalar field's internal
equation residual. It is not assumed as a conservation certificate. -/
theorem c2_normal_scalar_stress_divergence (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ : ℝ) (b : Fin 4) :
    coordinateDivergence g (scalarFieldStress g φ μ) 0 b =
      (scalarFieldWaveOperator g φ 0 - μ * φ 0) * scalarPartial φ 0 b := by
  rw [c2_normal_coordinateDivergence g germ, c2_normal_scalar_wave_operator g germ]
  simp_rw [c2_normal_scalar_stress_partial g germ φ hφ μ]
  exact scalar_source_balance_algebra (scalarPartial φ 0) (scalarSecondPartial φ 0)
    (c2_scalarSecondPartial_symmetric φ 0 hφ) (φ 0) μ b

theorem c2_normal_scalar_internal_equation_implies_conservation
    (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ : ℝ)
    (internal_equation : scalarFieldWaveOperator g φ 0 = μ * φ 0) :
    coordinateDivergence g (scalarFieldStress g φ μ) 0 = 0 := by
  funext b
  rw [c2_normal_scalar_stress_divergence g germ φ hφ μ b, internal_equation, sub_self, zero_mul]
  rfl

#print axioms scalar_source_balance_algebra
#print axioms c2_normal_scalar_wave_operator
#print axioms c2_normal_scalar_stress_divergence
#print axioms c2_normal_scalar_internal_equation_implies_conservation
end
end AASCSemanticExhaustion
