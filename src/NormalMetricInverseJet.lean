import C3NormalCurvatureDerivative

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

theorem c2_normal_metric_inverse_first_zero (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (a b : Fin 4) : fderiv ℝ (fun x => (g x)⁻¹ a b) 0 = 0 := by
  have nd : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hrow (i k : Fin 4) (v : CoordinatePoint) :
      (∑ j : Fin 4, metric i j * fderiv ℝ (fun x => (g x)⁻¹ j k) 0 v) = 0 := by
    have he : ∀ᶠ x in nhds 0,
        (∑ j : Fin 4, g x i j * (g x)⁻¹ j k) = (1 : Tensor2) i k := by
      have hs := c2_metric_nondegenerate_eventually g 0 germ.2.1 nd
      filter_upwards [hs] with x hx
      exact congrArg (fun A : Tensor2 => A i k)
        (Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr hx))
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((germ.2.1 i j).differentiableAt (by norm_num)).hasFDerivAt.mul
        (c2_metric_inverse_differentiableAt g 0 germ.2.1 nd j k).hasFDerivAt)
    have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he
    have hl := hs.fderiv
    change fderiv ℝ (fun x => ∑ j : Fin 4, g x i j * (g x)⁻¹ j k) 0 = _ at hl
    rw [hl] at hd
    have hconst : fderiv ℝ (fun _ : CoordinatePoint => (1 : Tensor2) i k) 0 = 0 := by simp
    rw [hconst] at hd
    have h := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D v) hd
    simpa only [Pi.mul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, germ.2.2.1, germ.2.2.2,
      ContinuousLinearMap.zero_apply, mul_zero, add_zero] using h
  apply ContinuousLinearMap.ext
  intro v
  have h := canonical_metric_double_contraction (fun j => fderiv ℝ (fun x => (g x)⁻¹ j b) 0 v) a
  simp_rw [hrow _ b v] at h
  simpa only [mul_zero, Finset.sum_const_zero, ContinuousLinearMap.zero_apply] using h.symm

theorem c2_normal_metric_inverse_hasFDerivAt_zero (g : MetricField) (germ : C2NormalizedMetricGerm g)
    (a b : Fin 4) : HasFDerivAt (𝕜 := ℝ) (fun x => (g x)⁻¹ a b) 0 0 := by
  have nd : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hd := (c2_metric_inverse_differentiableAt g 0 germ.2.1 nd a b).hasFDerivAt
  rw [c2_normal_metric_inverse_first_zero g germ] at hd
  exact hd

#print axioms c2_normal_metric_inverse_first_zero
#print axioms c2_normal_metric_inverse_hasFDerivAt_zero
end
end AASCSemanticExhaustion
