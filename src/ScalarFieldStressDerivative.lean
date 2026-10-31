import ScalarFieldSourceCalculus

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

def scalarFieldEnergy (g : MetricField) (φ : CoordinatePoint → ℝ) (μ : ℝ) (p : CoordinatePoint) : ℝ :=
  scalarFieldKinetic g φ p + μ * (φ p * φ p)

theorem c2_normal_scalar_energy_differentiable (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ : ℝ) :
    DifferentiableAt ℝ (scalarFieldEnergy g φ μ) 0 :=
  (c2_normal_scalar_kinetic_differentiable g germ φ hφ).add
    (((hφ.differentiableAt (by norm_num)).mul (hφ.differentiableAt (by norm_num))).const_mul μ)

theorem c2_normal_scalar_energy_partial (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ : ℝ) (c : Fin 4) :
    scalarPartial (scalarFieldEnergy g φ μ) 0 c =
      2 * (∑ a : Fin 4, metric a a * scalarPartial φ 0 a * scalarSecondPartial φ 0 a c) +
        2 * μ * φ 0 * scalarPartial φ 0 c := by
  have hf := hφ.differentiableAt (by norm_num)
  change scalarPartial (fun x => scalarFieldKinetic g φ x + μ * (φ x * φ x)) 0 c = _
  rw [scalarPartial_add_at_zero (scalarFieldKinetic g φ) (fun x => μ * (φ x * φ x))
    (c2_normal_scalar_kinetic_differentiable g germ φ hφ) ((hf.mul hf).const_mul μ) c]
  rw [c2_normal_scalar_kinetic_partial g germ φ hφ,
    scalarPartial_smul_at_zero μ (fun x => φ x * φ x) (hf.mul hf) c,
    scalar_partial_mul_at_zero φ φ hf hf c]
  ring

theorem c2_normal_scalar_stress_differentiable (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ : ℝ) (a b : Fin 4) :
    DifferentiableAt ℝ (fun x => scalarFieldStress g φ μ x a b) 0 := by
  exact ((c2_local_scalarPartial_differentiableAt φ 0 hφ a).mul
    (c2_local_scalarPartial_differentiableAt φ 0 hφ b)).sub
    ((((germ.2.1 a b).differentiableAt (by norm_num)).mul
      (c2_normal_scalar_energy_differentiable g germ φ hφ μ)).const_mul (1 / 2 : ℝ))

theorem c2_normal_scalar_stress_partial (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (μ : ℝ) (a b c : Fin 4) :
    scalarPartial (fun x => scalarFieldStress g φ μ x a b) 0 c =
      scalarPartial φ 0 a * scalarSecondPartial φ 0 b c +
      scalarPartial φ 0 b * scalarSecondPartial φ 0 a c -
      metric a b * ((∑ e : Fin 4, metric e e * scalarPartial φ 0 e * scalarSecondPartial φ 0 e c) +
        μ * φ 0 * scalarPartial φ 0 c) := by
  have ha := c2_local_scalarPartial_differentiableAt φ 0 hφ a
  have hb := c2_local_scalarPartial_differentiableAt φ 0 hφ b
  have hg := (germ.2.1 a b).differentiableAt (by norm_num)
  have hE := c2_normal_scalar_energy_differentiable g germ φ hφ μ
  change scalarPartial (fun x => scalarPartial φ x a * scalarPartial φ x b -
    (1 / 2 : ℝ) * (g x a b * scalarFieldEnergy g φ μ x)) 0 c = _
  rw [scalar_partial_sub_at_zero (fun x => scalarPartial φ x a * scalarPartial φ x b)
    (fun x => (1 / 2 : ℝ) * (g x a b * scalarFieldEnergy g φ μ x))
    (ha.mul hb) ((hg.mul hE).const_mul (1 / 2 : ℝ)) c,
    scalar_partial_mul_at_zero (fun x => scalarPartial φ x a) (fun x => scalarPartial φ x b) ha hb c,
    scalarPartial_smul_at_zero (1 / 2 : ℝ) (fun x => g x a b * scalarFieldEnergy g φ μ x) (hg.mul hE) c,
    scalar_partial_mul_at_zero (fun x => g x a b) (scalarFieldEnergy g φ μ) hg hE c,
    c2_normal_scalar_energy_partial g germ φ hφ μ c]
  have hz : scalarPartial (fun x => g x a b) 0 c = 0 := by
    unfold scalarPartial
    rw [germ.2.2.2]
    rfl
  change scalarPartial φ 0 a * scalarSecondPartial φ 0 b c +
    scalarPartial φ 0 b * scalarSecondPartial φ 0 a c - _ = _
  rw [hz, germ.2.2.1]
  ring

#print axioms c2_normal_scalar_energy_differentiable
#print axioms c2_normal_scalar_energy_partial
#print axioms c2_normal_scalar_stress_differentiable
#print axioms c2_normal_scalar_stress_partial
end
end AASCSemanticExhaustion
