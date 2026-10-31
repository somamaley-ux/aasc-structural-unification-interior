import OriginalCoordinateCurvatureIdentification

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

def C3NormalizedMetricGerm (g : MetricField) : Prop :=
  MetricFieldSymmetric g ∧ (∀ a b, ContDiffAt ℝ 3 (fun x => g x a b) 0) ∧
    g 0 = metric ∧ ∀ a b, fderiv ℝ (fun x => g x a b) 0 = 0

theorem c3_normalized_metric_c2 (g : MetricField) (germ : C3NormalizedMetricGerm g) :
    C2NormalizedMetricGerm g := by
  refine ⟨germ.1, ?_, germ.2.2.1, germ.2.2.2⟩
  intro a b
  exact (germ.2.1 a b).of_le (by norm_num)

def rawMetricHessian (g : MetricField) (p : CoordinatePoint) : Tensor4 := fun a b c d =>
  scalarSecondPartial (fun x => g x a b) p c d

theorem c3_metric_second_partial_differentiableAt (g : MetricField)
    (regular : ∀ a b, ContDiffAt ℝ 3 (fun x => g x a b) 0) (a b c d : Fin 4) :
    DifferentiableAt ℝ (fun x => rawMetricHessian g x a b c d) 0 :=
  c2_local_scalarPartial_differentiableAt _ 0 (c3_scalarPartial_c2 _ 0 (regular a b) c) d

def normalCurvatureDerivative (g : MetricField) (a b c d : Fin 4) : CoordinatePoint →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (fderiv ℝ (fun x => rawMetricHessian g x a d b c) 0 +
    fderiv ℝ (fun x => rawMetricHessian g x b c a d) 0 -
    fderiv ℝ (fun x => rawMetricHessian g x a c b d) 0 -
    fderiv ℝ (fun x => rawMetricHessian g x b d a c) 0)

theorem c3_hessian_curvature_hasFDerivAt (g : MetricField)
    (regular : ∀ a b, ContDiffAt ℝ 3 (fun x => g x a b) 0) (a b c d : Fin 4) :
    HasFDerivAt (fun x => curvatureOfNormalHessian (rawMetricHessian g x) a b c d)
      (normalCurvatureDerivative g a b c d) 0 := by
  have hd := ((((c3_metric_second_partial_differentiableAt g regular a d b c).hasFDerivAt.add
    (c3_metric_second_partial_differentiableAt g regular b c a d).hasFDerivAt).sub
      (c3_metric_second_partial_differentiableAt g regular a c b d).hasFDerivAt).sub
        (c3_metric_second_partial_differentiableAt g regular b d a c).hasFDerivAt).const_mul (1 / 2 : ℝ)
  simpa only [curvatureOfNormalHessian, normalCurvatureDerivative, Pi.add_apply, Pi.sub_apply] using hd

/-- Actual curvature derivative at a normal metric point. The derivative of
each quadratic connection correction vanishes because both connection values
vanish; it is not discarded by a normal-form definition. -/
theorem c3_normal_metric_curvature_hasFDerivAt (g : MetricField)
    (germ : C3NormalizedMetricGerm g) (a b c d : Fin 4) :
    HasFDerivAt (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d)
      (normalCurvatureDerivative g a b c d) 0 := by
  have germ2 := c3_normalized_metric_c2 g germ
  have nd : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hproduct (u v w z : Fin 4) : HasFDerivAt (𝕜 := ℝ)
      (fun x => ∑ k : Fin 4, leviCivitaCoefficients g x k u v * lowerChristoffel g x k w z) 0 0 := by
    have hd (k : Fin 4) := (c2_normalized_metric_christoffel_hasFDerivAt g germ2 k u v).mul
      (c2_metric_lowerChristoffel_hasFDerivAt g 0 germ2.2.1 k w z)
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => hd k)
    simpa only [Pi.mul_apply, c2_normalized_metric_christoffel_zero g germ2,
      c2_normalized_metric_lowerChristoffel_zero g germ2, zero_smul, add_zero,
      Finset.sum_const_zero] using hs
  have hc := ((c3_hessian_curvature_hasFDerivAt g germ.2.1 a b c d).add (hproduct a d b c)).sub
    (hproduct a c b d)
  have he : ∀ᶠ x in nhds 0,
      loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d =
        curvatureOfNormalHessian (rawMetricHessian g x) a b c d +
          (∑ k : Fin 4, leviCivitaCoefficients g x k a d * lowerChristoffel g x k b c) -
          (∑ k : Fin 4, leviCivitaCoefficients g x k a c * lowerChristoffel g x k b d) := by
    have hr : ∀ᶠ x in nhds 0, ∀ u v, ContDiffAt ℝ 2 (fun y => g y u v) x :=
      Filter.eventually_all.mpr (fun u => Filter.eventually_all.mpr (fun v =>
        ((germ.2.1 u v).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually (by norm_num)))
    have hn := c2_metric_nondegenerate_eventually g 0 germ2.2.1 nd
    filter_upwards [hr, hn] with x hx hnx
    exact c2_general_coordinate_curvature_formula g x germ.1 hx hnx a b c d
  have h := hc.congr_of_eventuallyEq he
  simpa only [add_zero, sub_zero] using h

theorem c3_normal_metric_curvature_partial (g : MetricField)
    (germ : C3NormalizedMetricGerm g) (a b c d e : Fin 4) :
    scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d) 0 e =
      (1 / 2 : ℝ) * (scalarThirdPartial (fun x => g x a d) 0 b c e +
        scalarThirdPartial (fun x => g x b c) 0 a d e -
        scalarThirdPartial (fun x => g x a c) 0 b d e -
        scalarThirdPartial (fun x => g x b d) 0 a c e) := by
  unfold scalarPartial
  rw [(c3_normal_metric_curvature_hasFDerivAt g germ a b c d).fderiv]
  simp only [normalCurvatureDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  rfl

theorem c3_normal_metric_differential_bianchi (g : MetricField)
    (germ : C3NormalizedMetricGerm g) (a b c d e : Fin 4) :
    scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d) 0 e +
      scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b d e) 0 c +
      scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b e c) 0 d = 0 := by
  rw [c3_normal_metric_curvature_partial g germ, c3_normal_metric_curvature_partial g germ,
    c3_normal_metric_curvature_partial g germ]
  linarith [scalarThirdPartial_swap_last (fun x => g x a d) 0 (germ.2.1 a d) b c e,
    scalarThirdPartial_swap_last (fun x => g x b c) 0 (germ.2.1 b c) a d e,
    scalarThirdPartial_swap_last (fun x => g x a c) 0 (germ.2.1 a c) b d e,
    scalarThirdPartial_swap_last (fun x => g x b d) 0 (germ.2.1 b d) a c e,
    scalarThirdPartial_swap_last (fun x => g x a e) 0 (germ.2.1 a e) b d c,
    scalarThirdPartial_swap_last (fun x => g x b e) 0 (germ.2.1 b e) a d c]

#print axioms c3_normalized_metric_c2
#print axioms c3_metric_second_partial_differentiableAt
#print axioms c3_hessian_curvature_hasFDerivAt
#print axioms c3_normal_metric_curvature_hasFDerivAt
#print axioms c3_normal_metric_curvature_partial
#print axioms c3_normal_metric_differential_bianchi
end
end AASCSemanticExhaustion
