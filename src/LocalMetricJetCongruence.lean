import C2LorentzMetricTransport
import GeneralNormalizedChartTransport

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem metric_twojet_of_eventuallyEq (g h : MetricField) (p : CoordinatePoint)
    (equal : ∀ᶠ x in nhds p, g x = h x) : MetricTwoJetEqualAt g h p := by
  have he (a b : Fin 4) : ∀ᶠ x in nhds p, g x a b = h x a b :=
    equal.mono (fun x hx => congrArg (fun M : Tensor2 => M a b) hx)
  refine ⟨Filter.EventuallyEq.eq_of_nhds equal, ?_, ?_⟩
  · intro a b
    exact Filter.EventuallyEq.fderiv_eq (he a b)
  · intro a b c d
    have hd : ∀ᶠ x in nhds p,
        scalarPartial (fun y => g y a b) x c = scalarPartial (fun y => h y a b) x c := by
      have hd := Filter.EventuallyEq.fderiv (𝕜 := ℝ) (he a b)
      exact hd.mono (fun x hx => congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1)) hx)
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single d 1))
      (Filter.EventuallyEq.fderiv_eq hd)

theorem c2_normalized_leviCivita_twojet_congr (g h : MetricField)
    (germG : C2NormalizedMetricGerm g) (germH : C2NormalizedMetricGerm h)
    (equal : MetricTwoJetEqualAt g h 0) :
    loweredConnectionCurvature g (leviCivitaCoefficients g) 0 =
      loweredConnectionCurvature h (leviCivitaCoefficients h) 0 := by
  rw [c2_normalized_metric_leviCivita_curvature g germG,
    c2_normalized_metric_leviCivita_curvature h germH]
  have hh : c2MetricHessian g 0 germG.1 germG.2.1 = c2MetricHessian h 0 germH.1 germH.2.1 := by
    apply Subtype.ext
    funext a b c d
    exact equal.2.2 a b c d
  change (curvatureJetMap _ : curvatureSpace).val = (curvatureJetMap _ : curvatureSpace).val
  rw [hh]

theorem coordinateMetricPullback_comp_eventually (g : MetricField)
    (F G : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (regularF : ContDiffAt ℝ 1 F (G p)) (regularG : ContDiffAt ℝ 1 G p) :
    ∀ᶠ x in nhds p, coordinateMetricPullback (coordinateMetricPullback g F) G x =
      coordinateMetricPullback g (fun y => F (G y)) x := by
  have hsF := (regularF.eventually (by norm_num)).filter_mono regularG.continuousAt
  have hsG := regularG.eventually (by norm_num)
  filter_upwards [hsF, hsG] with x hxF hxG
  change ContDiffAt ℝ 1 F (G x) at hxF
  rw [coordinateMetricPullback_matrix (coordinateMetricPullback g F) G x,
    coordinateMetricPullback_matrix g F (G x),
    coordinateMetricPullback_matrix g (fun y => F (G y)) x,
    coordinateJacobian_comp F G x (hxF.differentiableAt (by norm_num))
      (hxG.differentiableAt (by norm_num))]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

#print axioms metric_twojet_of_eventuallyEq
#print axioms c2_normalized_leviCivita_twojet_congr
#print axioms coordinateMetricPullback_comp_eventually
end
end AASCSemanticExhaustion
