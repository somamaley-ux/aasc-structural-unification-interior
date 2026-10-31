import LocalSecondJetCalculus
import CurvatureJetFrameNaturality

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem normalized_lorentz_pullback_first (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (L : LorentzComparison) (a b : Fin 4) :
    fderiv ℝ (fun x => coordinateMetricPullback g (lorentzCoordinateMap L) x a b) 0 = 0 := by
  have hb (i j : Fin 4) : HasFDerivAt (𝕜 := ℝ)
      (fun x => g (lorentzCoordinateMap L x) i j) 0 0 := by
    have hs : DifferentiableAt ℝ (fun x => g x i j) (lorentzCoordinateMap L 0) := by
      simpa only [lorentzCoordinateMap_zero] using
        (germ.2.1 i j).differentiableAt (by simp)
    have hd := hs.hasFDerivAt.comp 0 (lorentzCoordinateMap_hasFDerivAt L 0)
    change HasFDerivAt (fun x => g (lorentzCoordinateMap L x) i j)
      ((fderiv ℝ (fun x => g x i j) (lorentzCoordinateMap L 0)).comp
        (lorentzCoordinateEquiv L).toContinuousLinearMap) 0 at hd
    simpa only [lorentzCoordinateMap_zero, germ.2.2.2, ContinuousLinearMap.zero_comp] using hd
  have ht (i j : Fin 4) := ((hb i j).const_mul (L.forward i a)).mul_const (L.forward j b)
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht i j))
  have hd : HasFDerivAt (𝕜 := ℝ)
      (fun x => coordinateMetricPullback g (lorentzCoordinateMap L) x a b) 0 0 := by
    simpa only [coordinateMetricPullback, lorentzCoordinateMap_jacobian,
      smul_zero, Finset.sum_const_zero] using hs
  exact hd.fderiv

theorem normalized_lorentz_pullback_germ (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (L : LorentzComparison) :
    NormalizedSmoothMetricGerm (coordinateMetricPullback g (lorentzCoordinateMap L)) := by
  refine ⟨coordinateMetricPullback_symmetric g germ.1 _, ?_, ?_,
    normalized_lorentz_pullback_first g germ L⟩
  · apply coordinateMetricPullback_contDiffAt g _ 0 (lorentzCoordinateMap_smooth L).contDiffAt
    simpa only [lorentzCoordinateMap_zero] using germ.2.1
  · rw [coordinateMetricPullback_matrix, lorentzCoordinateMap_zero,
      lorentzCoordinateMap_jacobian, germ.2.2.1, L.metric_preserved]

theorem local_metric_lorentz_composition_second (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (L : LorentzComparison) (i j c d : Fin 4) :
    scalarSecondPartial (fun x => g (lorentzCoordinateMap L x) i j) 0 c d =
      ∑ u : Fin 4, ∑ v : Fin 4,
        scalarSecondPartial (fun x => g x i j) 0 u v * L.forward u c * L.forward v d := by
  have hs : ContDiffAt ℝ ⊤ (fun x => g x i j)
      ((lorentzCoordinateEquiv L).toContinuousLinearMap 0) := by
    simpa using germ.2.1 i j
  have h := local_linear_composition_second_coordinates (fun x => g x i j)
    (lorentzCoordinateEquiv L).toContinuousLinearMap 0 hs c d
  simp only [map_zero] at h
  change scalarSecondPartial (fun x => g (lorentzCoordinateMap L x) i j) 0 c d =
    ∑ u : Fin 4, ∑ v : Fin 4, scalarSecondPartial (fun x => g x i j) 0 u v *
      lorentzCoordinateEquiv L (Pi.single c 1) u *
        lorentzCoordinateEquiv L (Pi.single d 1) v at h
  simpa only [map_zero, lorentzCoordinateEquiv_basis] using h

theorem normalized_lorentz_pullback_second (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (L : LorentzComparison) (a b c d : Fin 4) :
    scalarSecondPartial (fun x => coordinateMetricPullback g (lorentzCoordinateMap L) x a b) 0 c d =
      pullbackFour L.forward (actualMetricHessian g 0 germ.1 germ.2.1) a b c d := by
  let B := fun i j x => g (lorentzCoordinateMap L x) i j
  let W := fun i j x => (L.forward i a * L.forward j b) * B i j x
  have hb (i j : Fin 4) : ContDiffAt ℝ ⊤ (B i j) 0 := by
    have hs : ContDiffAt ℝ ⊤ (fun x => g x i j) (lorentzCoordinateMap L 0) := by
      simpa only [lorentzCoordinateMap_zero] using germ.2.1 i j
    exact hs.comp 0 (lorentzCoordinateMap_smooth L).contDiffAt
  have hw (i j : Fin 4) : ContDiffAt ℝ ⊤ (W i j) 0 := contDiffAt_const.mul (hb i j)
  have ho (i : Fin 4) : ContDiffAt ℝ ⊤ (fun x => ∑ j, W i j x) 0 :=
    ContDiffAt.sum (fun j _ => hw i j)
  have heq : (fun x => coordinateMetricPullback g (lorentzCoordinateMap L) x a b) =
      (fun x => ∑ i : Fin 4, ∑ j : Fin 4, W i j x) := by
    funext x
    simp only [coordinateMetricPullback, lorentzCoordinateMap_jacobian, W, B]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, local_scalarSecondPartial_sum _ 0 ho c d]
  simp_rw [local_scalarSecondPartial_sum _ 0 (hw _) c d]
  have hW (i j : Fin 4) : scalarSecondPartial (W i j) 0 c d =
      (L.forward i a * L.forward j b) * scalarSecondPartial (B i j) 0 c d :=
    local_scalarSecondPartial_const_mul _ (B i j) 0 (hb i j) c d
  simp_rw [hW]
  dsimp only [B]
  simp_rw [local_metric_lorentz_composition_second g germ L]
  rw [pullbackFour_flat]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change _ = _ * scalarSecondPartial (fun x => g x i j) 0 u v
  ring

theorem normalized_lorentz_hessian_transport (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (L : LorentzComparison) :
    ((actualMetricHessian (coordinateMetricPullback g (lorentzCoordinateMap L)) 0
      (normalized_lorentz_pullback_germ g germ L).1
      (normalized_lorentz_pullback_germ g germ L).2.1 : metricHessianSpace) : Tensor4) =
        pullbackFour L.forward (actualMetricHessian g 0 germ.1 germ.2.1) := by
  funext a b c d
  exact normalized_lorentz_pullback_second g germ L a b c d

/-- Actual Levi-Civita curvature transforms tensorially for every normalized
smooth metric germ and every actual constant Lorentz coordinate change. -/
theorem normalized_leviCivita_lorentz_transport (g : MetricField)
    (germ : NormalizedSmoothMetricGerm g) (L : LorentzComparison) :
    loweredConnectionCurvature (coordinateMetricPullback g (lorentzCoordinateMap L))
      (leviCivitaCoefficients (coordinateMetricPullback g (lorentzCoordinateMap L))) 0 =
        pullbackFour L.forward (loweredConnectionCurvature g (leviCivitaCoefficients g) 0) := by
  rw [normalized_metric_leviCivita_curvature _ (normalized_lorentz_pullback_germ g germ L),
    normalized_metric_leviCivita_curvature g germ]
  change curvatureOfNormalHessian _ = pullbackFour L.forward (curvatureOfNormalHessian _)
  rw [normalized_lorentz_hessian_transport g germ L, curvatureOfNormalHessian_pullback]

#print axioms normalized_lorentz_pullback_first
#print axioms normalized_lorentz_pullback_germ
#print axioms local_metric_lorentz_composition_second
#print axioms normalized_lorentz_pullback_second
#print axioms normalized_lorentz_hessian_transport
#print axioms normalized_leviCivita_lorentz_transport
end
end AASCSemanticExhaustion
