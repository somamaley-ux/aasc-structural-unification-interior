import DifferentiableTensorDivergence
import C2LocalSecondJetCalculus

/-! Module A 13.3, actual local scalar-field source calculation.
This step derives the divergence source term from actual derivatives; it will
not assume conservation of the scalar stress tensor. Action differentiation and
native source-protocol ancestry are distinct attachments. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped BigOperators

def scalarFieldKinetic (g : MetricField) (φ : CoordinatePoint → ℝ) (p : CoordinatePoint) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, (g p)⁻¹ a b * scalarPartial φ p a * scalarPartial φ p b

def scalarFieldStress (g : MetricField) (φ : CoordinatePoint → ℝ) (massSquared : ℝ) : MetricField :=
  fun p a b => scalarPartial φ p a * scalarPartial φ p b -
    (1 / 2 : ℝ) * (g p a b * (scalarFieldKinetic g φ p + massSquared * (φ p * φ p)))

theorem scalar_partial_mul_at_zero (f h : CoordinatePoint → ℝ)
    (hf : DifferentiableAt ℝ f 0) (hh : DifferentiableAt ℝ h 0) (c : Fin 4) :
    scalarPartial (fun x => f x * h x) 0 c =
      f 0 * scalarPartial h 0 c + h 0 * scalarPartial f 0 c := by
  have hd := (hf.hasFDerivAt.mul hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x * h x) 0 = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem scalar_partial_sub_at_zero (f h : CoordinatePoint → ℝ)
    (hf : DifferentiableAt ℝ f 0) (hh : DifferentiableAt ℝ h 0) (c : Fin 4) :
    scalarPartial (fun x => f x - h x) 0 c = scalarPartial f 0 c - scalarPartial h 0 c := by
  have hd := (hf.hasFDerivAt.sub hh.hasFDerivAt).fderiv
  change fderiv ℝ (fun x => f x - h x) 0 = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.sub_apply]

theorem c2_normal_scalar_kinetic_differentiable (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) :
    DifferentiableAt ℝ (scalarFieldKinetic g φ) 0 := by
  apply DifferentiableAt.fun_sum
  intro a _
  apply DifferentiableAt.fun_sum
  intro b _
  exact (((c2_normal_metric_inverse_hasFDerivAt_zero g germ a b).differentiableAt.mul
    (c2_local_scalarPartial_differentiableAt φ 0 hφ a)).mul
    (c2_local_scalarPartial_differentiableAt φ 0 hφ b))

theorem c2_normal_scalar_kinetic_partial (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (φ : CoordinatePoint → ℝ) (hφ : ContDiffAt ℝ 2 φ 0) (c : Fin 4) :
    scalarPartial (scalarFieldKinetic g φ) 0 c =
      2 * ∑ a : Fin 4, metric a a * scalarPartial φ 0 a * scalarSecondPartial φ 0 a c := by
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      (((c2_normal_metric_inverse_hasFDerivAt_zero g germ a b).mul
        (c2_local_scalarPartial_differentiableAt φ 0 hφ a).hasFDerivAt).mul
        (c2_local_scalarPartial_differentiableAt φ 0 hφ b).hasFDerivAt)))).fderiv
  change fderiv ℝ (scalarFieldKinetic g φ) 0 = _ at hd
  simp only [scalarPartial, hd, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply,
    mul_zero, add_zero, Pi.mul_apply, germ.2.2.1, canonical_metric_inverse]
  change (∑ a : Fin 4, ∑ b : Fin 4,
    ((metric a b * scalarPartial φ 0 a) * scalarSecondPartial φ 0 b c +
      scalarPartial φ 0 b * (metric a b * scalarSecondPartial φ 0 a c))) = _
  have hc := canonical_metric_contraction_diagonal
    (fun a b => scalarPartial φ 0 a * scalarSecondPartial φ 0 b c +
      scalarPartial φ 0 b * scalarSecondPartial φ 0 a c)
  have he : (∑ a : Fin 4, ∑ b : Fin 4,
      ((metric a b * scalarPartial φ 0 a) * scalarSecondPartial φ 0 b c +
        scalarPartial φ 0 b * (metric a b * scalarSecondPartial φ 0 a c))) =
      ∑ a : Fin 4, ∑ b : Fin 4, metric a b *
        (scalarPartial φ 0 a * scalarSecondPartial φ 0 b c +
          scalarPartial φ 0 b * scalarSecondPartial φ 0 a c) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he, hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [scalarPartial]
  ring

#print axioms scalar_partial_mul_at_zero
#print axioms scalar_partial_sub_at_zero
#print axioms c2_normal_scalar_kinetic_differentiable
#print axioms c2_normal_scalar_kinetic_partial
end
end AASCSemanticExhaustion
