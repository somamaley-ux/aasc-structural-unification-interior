import CoordinateChartTransition

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem pointNormalChartInverse_right_inverse (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    ∀ᶠ y in nhds p, pointNormalChartMap g p B (pointNormalChartInverse g p B symmetric y) = y := by
  have hs := (pointNormalChartMap_analytic g p B).contDiffAt.hasStrictFDerivAt'
    (pointNormalChartMap_hasFDerivAt g p B symmetric) (by simp)
  simpa only [pointNormalChartMap_zero] using hs.eventually_right_inverse

def pointNormalChartTransition (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    CoordinatePoint → CoordinatePoint := fun x =>
      pointNormalChartInverse g p B symmetric (pointNormalChartMap g p C x)

theorem pointNormalChartTransition_zero (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    pointNormalChartTransition g p B C symmetric 0 = 0 := by
  simp [pointNormalChartTransition, pointNormalChartMap_zero, pointNormalChartInverse_at_point]

theorem pointNormalChartTransition_analytic (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    ContDiffAt ℝ ⊤ (pointNormalChartTransition g p B C symmetric) 0 := by
  have hi : ContDiffAt ℝ ⊤ (pointNormalChartInverse g p B symmetric)
      (pointNormalChartMap g p C 0) := by
    simpa only [pointNormalChartMap_zero] using pointNormalChartInverse_analytic g p B symmetric
  exact hi.comp 0 (pointNormalChartMap_analytic g p C).contDiffAt

theorem pointNormalChartTransition_comp_eventually (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    ∀ᶠ x in nhds 0, pointNormalChartMap g p B (pointNormalChartTransition g p B C symmetric x) =
      pointNormalChartMap g p C x := by
  have hc : Filter.Tendsto (pointNormalChartMap g p C) (nhds 0) (nhds p) := by
    have h := (pointNormalChartMap_analytic g p C).continuous.continuousAt (x := 0)
    change Filter.Tendsto (pointNormalChartMap g p C) (nhds 0)
      (nhds (pointNormalChartMap g p C 0)) at h
    simpa only [pointNormalChartMap_zero] using h
  exact (pointNormalChartInverse_right_inverse g p B symmetric).filter_mono hc

theorem pointNormalChartTransition_metric_eventually (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    ∀ᶠ x in nhds 0,
      coordinateMetricPullback (pointNormalizedMetric g p B) (pointNormalChartTransition g p B C symmetric) x =
        pointNormalizedMetric g p C x := by
  have hcomp := coordinateMetricPullback_comp_eventually g (pointNormalChartMap g p B)
    (pointNormalChartTransition g p B C symmetric) 0
      ((pointNormalChartMap_analytic g p B).contDiffAt.of_le (by simp))
      ((pointNormalChartTransition_analytic g p B C symmetric).of_le (by simp))
  have he := metric_pullback_congr_map_eventually g
    (fun x => pointNormalChartMap g p B (pointNormalChartTransition g p B C symmetric x))
    (pointNormalChartMap g p C) 0 (pointNormalChartTransition_comp_eventually g p B C symmetric)
  have h := hcomp.and he |>.mono (fun x hx => hx.1.trans hx.2)
  simpa only [pointNormalChartMap_pullback] using h

/-- The particular normal charts used by the envelope theorem have actual
analytic transitions, and their actual curvature values transform tensorially.
No selection of a normal chart is granted physical standing. -/
theorem c2_point_normal_chart_curvature_comparison (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (regular : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p)
    (frameB : LorentzFrameAt g p B) (frameC : LorentzFrameAt g p C) :
    ((c2_normalChartCurvature g p C symmetric regular frameC : curvatureSpace) : Tensor4) =
      pullbackFour (coordinateJacobian (pointNormalChartTransition g p B C symmetric) 0)
        (c2_normalChartCurvature g p B symmetric regular frameB) := by
  let hB := pointNormalizedMetric g p B
  let hC := pointNormalizedMetric g p C
  let T := pointNormalChartTransition g p B C symmetric
  have germB : C2NormalizedMetricGerm hB := c2_pointNormalizedMetric_germ g p B symmetric regular frameB
  have germC : C2NormalizedMetricGerm hC := c2_pointNormalizedMetric_germ g p C symmetric regular frameC
  have regularT : ContDiffAt ℝ 3 T 0 :=
    (pointNormalChartTransition_analytic g p B C symmetric).of_le (by simp)
  have zeroT : T 0 = 0 := pointNormalChartTransition_zero g p B C symmetric
  have equal := metric_twojet_of_eventuallyEq (coordinateMetricPullback hB T) hC 0
    (pointNormalChartTransition_metric_eventually g p B C symmetric)
  have germBT : C2NormalizedMetricGerm (coordinateMetricPullback hB T) := by
    refine ⟨coordinateMetricPullback_symmetric hB germB.1 _, ?_, equal.1.trans germC.2.2.1, ?_⟩
    · apply c3_coordinateMetricPullback_c2 hB T regularT
      simpa only [zeroT] using germB.2.1
    · intro a b
      exact (equal.2.1 a b).trans (germC.2.2.2 a b)
  have hc := c2_normalized_leviCivita_twojet_congr (coordinateMetricPullback hB T) hC germBT germC equal
  have ht := c2_normal_chart_curvature_transport hB germB T regularT zeroT germBT
  exact hc.symm.trans ht

theorem pointNormalChartTransition_frame_equation (g : MetricField) (p : CoordinatePoint)
    (B C : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    coordinateFrameMatrix B * coordinateJacobian (pointNormalChartTransition g p B C symmetric) 0 =
      coordinateFrameMatrix C := by
  let T := pointNormalChartTransition g p B C symmetric
  have ht : T 0 = 0 := pointNormalChartTransition_zero g p B C symmetric
  have heq : coordinateJacobian (fun x => pointNormalChartMap g p B (T x)) 0 =
      coordinateJacobian (pointNormalChartMap g p C) 0 := by
    ext i a
    have he : ∀ᶠ x in nhds 0,
        pointNormalChartMap g p B (T x) i = pointNormalChartMap g p C x i :=
      (pointNormalChartTransition_comp_eventually g p B C symmetric).mono
        (fun x hx => congrArg (fun v : CoordinatePoint => v i) hx)
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single a 1))
      (Filter.EventuallyEq.fderiv_eq he)
  rw [coordinateJacobian_comp _ _ 0 ((pointNormalChartMap_analytic g p B).differentiable
    (by simp) _) ((pointNormalChartTransition_analytic g p B C symmetric).differentiableAt (by simp)),
    pointNormalChartTransition_zero g p B C symmetric, pointNormalChartMap_jacobian g p B symmetric,
    pointNormalChartMap_jacobian g p C symmetric] at heq
  exact heq

#print axioms pointNormalChartInverse_right_inverse
#print axioms pointNormalChartTransition_zero
#print axioms pointNormalChartTransition_analytic
#print axioms pointNormalChartTransition_comp_eventually
#print axioms pointNormalChartTransition_metric_eventually
#print axioms c2_point_normal_chart_curvature_comparison
#print axioms pointNormalChartTransition_frame_equation
end
end AASCSemanticExhaustion
