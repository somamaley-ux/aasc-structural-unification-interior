import LocalMetricJetCongruence
import NormalChartSecondJet

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def residualCoordinateMap (L : LorentzComparison) (F : CoordinatePoint → CoordinatePoint) :
    CoordinatePoint → CoordinatePoint := fun x => (lorentzCoordinateEquiv L).symm (F x)

theorem residualCoordinateMap_c3 (L : LorentzComparison) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) : ContDiffAt ℝ 3 (residualCoordinateMap L F) 0 :=
  (lorentzCoordinateEquiv L).symm.contDiff.contDiffAt.comp 0 regular

theorem residualCoordinateMap_zero (L : LorentzComparison) (F : CoordinatePoint → CoordinatePoint)
    (zero : F 0 = 0) : residualCoordinateMap L F 0 = 0 := by
  simp [residualCoordinateMap, zero]

theorem residualCoordinateMap_first (L : LorentzComparison) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0)
    (first : fderiv ℝ F 0 = (lorentzCoordinateEquiv L).toContinuousLinearMap) :
    fderiv ℝ (residualCoordinateMap L F) 0 = ContinuousLinearMap.id ℝ CoordinatePoint := by
  have hd := (lorentzCoordinateEquiv L).symm.toContinuousLinearMap.hasFDerivAt.comp 0
    (regular.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (residualCoordinateMap L F)
    ((lorentzCoordinateEquiv L).symm.toContinuousLinearMap.comp (fderiv ℝ F 0)) 0 at hd
  rw [hd.fderiv, first]
  ext x i
  simp

theorem residualCoordinateMap_pullback_eventually (g : MetricField) (L : LorentzComparison)
    (F : CoordinatePoint → CoordinatePoint) (regular : ContDiffAt ℝ 3 F 0) :
    ∀ᶠ x in nhds 0,
      coordinateMetricPullback (coordinateMetricPullback g (lorentzCoordinateMap L))
        (residualCoordinateMap L F) x = coordinateMetricPullback g F x := by
  have hs := coordinateMetricPullback_comp_eventually g (lorentzCoordinateMap L)
    (residualCoordinateMap L F) 0 ((lorentzCoordinateMap_smooth L).contDiffAt.of_le (by simp))
      ((residualCoordinateMap_c3 L F regular).of_le (by norm_num))
  have he : (fun y => lorentzCoordinateMap L (residualCoordinateMap L F y)) = F := by
    funext y
    change lorentzCoordinateEquiv L ((lorentzCoordinateEquiv L).symm (F y)) = F y
    simp
  simpa only [he] using hs

/-- Between arbitrary normal coordinate germs, actual Levi-Civita curvature
has the four-index tensor pullback. The second coordinate jet is derived from
metric normality; no curvature-transformation bridge is assumed. -/
theorem c2_normal_chart_frame_curvature_transport (g : MetricField)
    (germ : C2NormalizedMetricGerm g) (F : CoordinatePoint → CoordinatePoint)
    (regular : ContDiffAt ℝ 3 F 0) (zero : F 0 = 0) (L : LorentzComparison)
    (first : fderiv ℝ F 0 = (lorentzCoordinateEquiv L).toContinuousLinearMap)
    (normal : C2NormalizedMetricGerm (coordinateMetricPullback g F)) :
    loweredConnectionCurvature (coordinateMetricPullback g F)
      (leviCivitaCoefficients (coordinateMetricPullback g F)) 0 =
        pullbackFour L.forward (loweredConnectionCurvature g (leviCivitaCoefficients g) 0) := by
  let h := coordinateMetricPullback g (lorentzCoordinateMap L)
  let G := residualCoordinateMap L F
  have germH : C2NormalizedMetricGerm h := c2_normalized_lorentz_pullback_germ g germ L
  have regularG : ContDiffAt ℝ 3 G 0 := residualCoordinateMap_c3 L F regular
  have zeroG : G 0 = 0 := residualCoordinateMap_zero L F zero
  have firstG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ CoordinatePoint :=
    residualCoordinateMap_first L F regular first
  have equal := metric_twojet_of_eventuallyEq (coordinateMetricPullback h G)
    (coordinateMetricPullback g F) 0 (residualCoordinateMap_pullback_eventually g L F regular)
  have germHG : C2NormalizedMetricGerm (coordinateMetricPullback h G) := by
    refine ⟨coordinateMetricPullback_symmetric h germH.1 _, ?_,
      equal.1.trans normal.2.2.1, ?_⟩
    · apply c3_coordinateMetricPullback_c2 h G regularG
      simpa only [zeroG] using germH.2.1
    · intro a b
      exact (equal.2.1 a b).trans (normal.2.2.2 a b)
  have hcurv := c2_normalized_leviCivita_twojet_congr (coordinateMetricPullback h G)
    (coordinateMetricPullback g F) germHG normal equal
  have hn := c2_normal_chart_identity_frame_curvature_transport h germH G regularG
    zeroG firstG germHG.2.2.2
  exact hcurv.symm.trans (hn.trans (c2_normalized_leviCivita_lorentz_transport g germ L))

#print axioms residualCoordinateMap_c3
#print axioms residualCoordinateMap_zero
#print axioms residualCoordinateMap_first
#print axioms residualCoordinateMap_pullback_eventually
#print axioms c2_normal_chart_frame_curvature_transport
end
end AASCSemanticExhaustion
