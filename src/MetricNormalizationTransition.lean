import C2GeneralCurvatureJetCongruence

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

theorem general_normalizing_chart_hasFDerivAt (g : MetricField) :
    HasFDerivAt (normalizingCoordinateMap g)
      (ContinuousLinearEquiv.refl ℝ CoordinatePoint).toContinuousLinearMap 0 :=
  quadraticCoordinateMap_hasFDerivAt_zero 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) _

def generalNormalizingChartInverse (g : MetricField) : CoordinatePoint → CoordinatePoint :=
  (normalizingCoordinateMap_smooth g).contDiffAt.localInverse
    (general_normalizing_chart_hasFDerivAt g) (by simp)

theorem generalNormalizingChartInverse_zero (g : MetricField) : generalNormalizingChartInverse g 0 = 0 := by
  have h := (normalizingCoordinateMap_smooth g).contDiffAt.localInverse_apply_image
    (general_normalizing_chart_hasFDerivAt g) (by simp)
  simpa only [normalizingCoordinateMap_zero] using h

theorem generalNormalizingChartInverse_analytic (g : MetricField) :
    ContDiffAt ℝ ⊤ (generalNormalizingChartInverse g) 0 := by
  have h := (normalizingCoordinateMap_smooth g).contDiffAt.to_localInverse
    (general_normalizing_chart_hasFDerivAt g) (by simp)
  simpa only [normalizingCoordinateMap_zero] using h

theorem generalNormalizingChartInverse_hasFDerivAt (g : MetricField) :
    HasFDerivAt (generalNormalizingChartInverse g) (ContinuousLinearMap.id ℝ CoordinatePoint) 0 := by
  have hs := (normalizingCoordinateMap_smooth g).contDiffAt.hasStrictFDerivAt'
    (general_normalizing_chart_hasFDerivAt g) (by simp)
  have h := hs.to_localInverse.hasFDerivAt
  simpa only [normalizingCoordinateMap_zero] using h

theorem generalNormalizingChartInverse_right_inverse (g : MetricField) :
    ∀ᶠ y in nhds 0, normalizingCoordinateMap g (generalNormalizingChartInverse g y) = y := by
  have hs := (normalizingCoordinateMap_smooth g).contDiffAt.hasStrictFDerivAt'
    (general_normalizing_chart_hasFDerivAt g) (by simp)
  simpa only [normalizingCoordinateMap_zero] using hs.eventually_right_inverse

def metricNormalizationTransition (g : MetricField) (F : CoordinatePoint → CoordinatePoint) :
    CoordinatePoint → CoordinatePoint := fun x =>
      generalNormalizingChartInverse g (F (normalizingCoordinateMap (coordinateMetricPullback g F) x))

theorem metricNormalizationTransition_zero (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (zero : F 0 = 0) : metricNormalizationTransition g F 0 = 0 := by
  simp [metricNormalizationTransition, normalizingCoordinateMap_zero, zero, generalNormalizingChartInverse_zero]

theorem metricNormalizationTransition_c3 (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (zero : F 0 = 0) :
    ContDiffAt ℝ 3 (metricNormalizationTransition g F) 0 := by
  have hF : ContDiffAt ℝ 3 F (normalizingCoordinateMap (coordinateMetricPullback g F) 0) := by
    simpa only [normalizingCoordinateMap_zero] using regular
  have hi : ContDiffAt ℝ 3 (generalNormalizingChartInverse g)
      (F (normalizingCoordinateMap (coordinateMetricPullback g F) 0)) := by
    simpa only [normalizingCoordinateMap_zero, zero] using
      (generalNormalizingChartInverse_analytic g).of_le (show (3 : WithTop ℕ∞) ≤ ⊤ by simp)
  exact hi.comp 0 (hF.comp 0 ((normalizingCoordinateMap_smooth _).contDiffAt.of_le (by simp)))

theorem metricNormalizationTransition_hasFDerivAt (g : MetricField) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (zero : F 0 = 0)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (derivative : HasFDerivAt F B.toContinuousLinearMap 0) :
    HasFDerivAt (metricNormalizationTransition g F) B.toContinuousLinearMap 0 := by
  have hF : HasFDerivAt F B.toContinuousLinearMap (normalizingCoordinateMap (coordinateMetricPullback g F) 0) := by
    simpa only [normalizingCoordinateMap_zero] using derivative
  have hi : HasFDerivAt (generalNormalizingChartInverse g) (ContinuousLinearMap.id ℝ CoordinatePoint)
      (F (normalizingCoordinateMap (coordinateMetricPullback g F) 0)) := by
    simpa only [normalizingCoordinateMap_zero, zero] using generalNormalizingChartInverse_hasFDerivAt g
  have h := hi.comp 0 (hF.comp 0 (general_normalizing_chart_hasFDerivAt _))
  simpa only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] using h

theorem metricNormalizationTransition_metric_eventually (g : MetricField)
    (F : CoordinatePoint → CoordinatePoint) (regular : ContDiffAt ℝ 3 F 0) (zero : F 0 = 0) :
    ∀ᶠ x in nhds 0,
      coordinateMetricPullback (coordinateMetricPullback g (normalizingCoordinateMap g))
        (metricNormalizationTransition g F) x =
      coordinateMetricPullback (coordinateMetricPullback g F)
        (normalizingCoordinateMap (coordinateMetricPullback g F)) x := by
  let N := normalizingCoordinateMap (coordinateMetricPullback g F)
  let T := metricNormalizationTransition g F
  have zeroN : N 0 = 0 := normalizingCoordinateMap_zero _
  have zeroT : T 0 = 0 := metricNormalizationTransition_zero g F zero
  have hFN : ContDiffAt ℝ 3 (fun x => F (N x)) 0 := by
    have hf : ContDiffAt ℝ 3 F (N 0) := by simpa only [zeroN] using regular
    exact hf.comp 0 ((normalizingCoordinateMap_smooth _).contDiffAt.of_le (by simp))
  have hmaps : ∀ᶠ x in nhds 0, normalizingCoordinateMap g (T x) = F (N x) := by
    have hc := hFN.continuousAt
    change Filter.Tendsto (fun x => F (N x)) (nhds 0) (nhds (F (N 0))) at hc
    rw [zeroN, zero] at hc
    exact (generalNormalizingChartInverse_right_inverse g).filter_mono hc
  have hleft := coordinateMetricPullback_comp_eventually g (normalizingCoordinateMap g) T 0
    ((normalizingCoordinateMap_smooth g).contDiffAt.of_le (by simp))
      ((metricNormalizationTransition_c3 g F regular zero).of_le (by norm_num))
  have hmiddle := metric_pullback_congr_map_eventually g
    (fun x => normalizingCoordinateMap g (T x)) (fun x => F (N x)) 0 hmaps
  have hright := coordinateMetricPullback_comp_eventually g F N 0
    (by simpa only [zeroN] using regular.of_le (show (1 : WithTop ℕ∞) ≤ 3 by norm_num))
      ((normalizingCoordinateMap_smooth _).contDiffAt.of_le (by simp))
  exact (hleft.and (hmiddle.and hright)).mono (fun x hx => hx.1.trans (hx.2.1.trans hx.2.2.symm))

#print axioms general_normalizing_chart_hasFDerivAt
#print axioms generalNormalizingChartInverse_zero
#print axioms generalNormalizingChartInverse_analytic
#print axioms generalNormalizingChartInverse_hasFDerivAt
#print axioms generalNormalizingChartInverse_right_inverse
#print axioms metricNormalizationTransition_zero
#print axioms metricNormalizationTransition_c3
#print axioms metricNormalizationTransition_hasFDerivAt
#print axioms metricNormalizationTransition_metric_eventually
end
end AASCSemanticExhaustion
