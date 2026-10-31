import C3NormalCurvatureDerivative
import CurvatureTensorPullbackLaws

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem c2_actual_curvature_algebraic_at_origin (g : MetricField)
    (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) 0)
    (nondegenerate : (g 0).det ≠ 0) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) 0 ∈ curvatureSpace := by
  let h := coordinateMetricPullback g (normalizingCoordinateMap g)
  have symH : MetricFieldSymmetric h := coordinateMetricPullback_symmetric g symmetric _
  have regH := c2_general_normalizing_metric_regular g regular
  have ndH : (h 0).det ≠ 0 := by
    change (coordinateMetricPullback g (normalizingCoordinateMap g) 0).det ≠ 0
    rw [general_normalizing_metric_value g symmetric]
    exact nondegenerate
  have he : loweredConnectionCurvature h (leviCivitaCoefficients h) 0 =
      curvatureOfNormalHessian (c2MetricHessian h 0 symH regH) := by
    funext a b c d
    exact c2_first_flat_metric_curvature h symH regH ndH
      (c2_general_normalizing_metric_first_zero g symmetric regular nondegenerate) a b c d
  have hp := c2_normalizing_actual_curvature_preserved g symmetric regular nondegenerate
  rw [← hp, he]
  exact hessian_curvature_mem (c2MetricHessian h 0 symH regH)

theorem c2_actual_curvature_algebraic (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) p ∈ curvatureSpace := by
  have symT : MetricFieldSymmetric (fun x => g (x + p)) := fun x a b => symmetric (x + p) a b
  have ndT : ((fun x => g (x + p)) 0).det ≠ 0 := by simpa only [zero_add] using nondegenerate
  have h := c2_actual_curvature_algebraic_at_origin (fun x => g (x + p)) symT
    (c2_metric_translated_regular g p regular) ndT
  rw [c2_coordinate_curvature_translation g p symmetric regular nondegenerate] at h
  exact h

def actualConnectionCurvature (g : MetricField) (p : CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (nondegenerate : (g p).det ≠ 0) : curvatureSpace :=
  ⟨loweredConnectionCurvature g (leviCivitaCoefficients g) p,
    c2_actual_curvature_algebraic g p symmetric regular nondegenerate⟩

theorem c3_normal_metric_curvature_laws_eventually (g : MetricField) (germ : C3NormalizedMetricGerm g) :
    ∀ᶠ x in nhds 0, loweredConnectionCurvature g (leviCivitaCoefficients g) x ∈ curvatureSpace := by
  have hr : ∀ᶠ x in nhds 0, ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) x :=
    Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (fun b =>
      ((germ.2.1 a b).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually (by norm_num)))
  have nd : (g 0).det ≠ 0 := by rw [germ.2.2.1, canonical_lorentz_metric_det]; norm_num
  have hn := c2_metric_nondegenerate_eventually g 0 (c3_normalized_metric_c2 g germ).2.1 nd
  filter_upwards [hr, hn] with x hx hnx
  exact c2_actual_curvature_algebraic g x germ.1 hx hnx

theorem c3_normal_curvature_partial_skew_first (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (a b c d e : Fin 4) :
    scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d) 0 e =
      -scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x b a c d) 0 e := by
  have he : ∀ᶠ x in nhds 0,
      loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d =
        -loweredConnectionCurvature g (leviCivitaCoefficients g) x b a c d :=
    (c3_normal_metric_curvature_laws_eventually g germ).mono (fun x hx => hx.1 a b c d)
  have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he
  have hn := ((c3_normal_metric_curvature_hasFDerivAt g germ b a c d).neg).fderiv
  change fderiv ℝ (fun x => -loweredConnectionCurvature g (leviCivitaCoefficients g) x b a c d) 0 = _ at hn
  rw [hn] at hd
  have h := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single e 1)) hd
  simpa only [scalarPartial, (c3_normal_metric_curvature_hasFDerivAt g germ b a c d).fderiv,
    ContinuousLinearMap.neg_apply] using h

theorem c3_normal_curvature_partial_skew_last (g : MetricField) (germ : C3NormalizedMetricGerm g)
    (a b c d e : Fin 4) :
    scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d) 0 e =
      -scalarPartial (fun x => loweredConnectionCurvature g (leviCivitaCoefficients g) x a b d c) 0 e := by
  have he : ∀ᶠ x in nhds 0,
      loweredConnectionCurvature g (leviCivitaCoefficients g) x a b c d =
        -loweredConnectionCurvature g (leviCivitaCoefficients g) x a b d c :=
    (c3_normal_metric_curvature_laws_eventually g germ).mono (fun x hx => hx.2.1 a b c d)
  have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he
  have hn := ((c3_normal_metric_curvature_hasFDerivAt g germ a b d c).neg).fderiv
  change fderiv ℝ (fun x => -loweredConnectionCurvature g (leviCivitaCoefficients g) x a b d c) 0 = _ at hn
  rw [hn] at hd
  have h := congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single e 1)) hd
  simpa only [scalarPartial, (c3_normal_metric_curvature_hasFDerivAt g germ a b d c).fderiv,
    ContinuousLinearMap.neg_apply] using h

#print axioms c2_actual_curvature_algebraic_at_origin
#print axioms c2_actual_curvature_algebraic
#print axioms c3_normal_metric_curvature_laws_eventually
#print axioms c3_normal_curvature_partial_skew_first
#print axioms c3_normal_curvature_partial_skew_last
end
end AASCSemanticExhaustion
