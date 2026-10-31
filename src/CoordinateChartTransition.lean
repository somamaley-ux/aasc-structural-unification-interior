import NormalChartComparison

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem metric_pullback_congr_map_eventually (g : MetricField)
    (F G : CoordinatePoint → CoordinatePoint) (p : CoordinatePoint)
    (equal : ∀ᶠ x in nhds p, F x = G x) :
    ∀ᶠ x in nhds p, coordinateMetricPullback g F x = coordinateMetricPullback g G x := by
  have hj (i a : Fin 4) : ∀ᶠ x in nhds p, coordinateJacobian F x i a = coordinateJacobian G x i a := by
    have he : ∀ᶠ x in nhds p, F x i = G x i :=
      equal.mono (fun x hx => congrArg (fun v : CoordinatePoint => v i) hx)
    have hd := Filter.EventuallyEq.fderiv (𝕜 := ℝ) he
    exact hd.mono (fun x hx => congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single a 1)) hx)
  have hall : ∀ᶠ x in nhds p, ∀ i a, coordinateJacobian F x i a = coordinateJacobian G x i a :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hj i))
  filter_upwards [equal, hall] with x hx hJ
  ext a b
  simp only [coordinateMetricPullback, hx, hJ]

theorem coordinate_derivative_of_frame_jacobian (F : CoordinatePoint → CoordinatePoint)
    (regular : DifferentiableAt ℝ F 0) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (jacobian : coordinateJacobian F 0 = coordinateFrameMatrix B) :
    fderiv ℝ F 0 = B.toContinuousLinearMap := by
  have hb (a : Fin 4) : fderiv ℝ F 0 (Pi.single a 1) = B (Pi.single a 1) := by
    ext i
    rw [← coordinateJacobian_vector F 0 regular, jacobian]
    rfl
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ F 0 v = B v
  have h := continuousLinearMap_four_coordinates (fderiv ℝ F 0).toLinearMap v
  have h' := continuousLinearMap_four_coordinates B.toContinuousLinearMap.toLinearMap v
  change fderiv ℝ F 0 v = ∑ a : Fin 4, v a • fderiv ℝ F 0 (Pi.single a 1) at h
  change B v = ∑ a : Fin 4, v a • B (Pi.single a 1) at h'
  rw [h, h']
  simp_rw [hb]

theorem pointNormalChartMap_analytic (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : ContDiff ℝ ⊤ (pointNormalChartMap g p B) :=
  (affineCoordinateMap_smooth p B).comp (normalizingCoordinateMap_smooth (framedMetricField g p B))

theorem pointNormalChartMap_hasFDerivAt (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    HasFDerivAt (pointNormalChartMap g p B) B.toContinuousLinearMap 0 := by
  have h := (pointNormalChartMap_analytic g p B).differentiable (by simp) 0
  have hd := coordinate_derivative_of_frame_jacobian (pointNormalChartMap g p B) h B
    (pointNormalChartMap_jacobian g p B symmetric)
  simpa only [hd] using h.hasFDerivAt

def pointNormalChartInverse (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    CoordinatePoint → CoordinatePoint :=
  (pointNormalChartMap_analytic g p B).contDiffAt.localInverse
    (pointNormalChartMap_hasFDerivAt g p B symmetric) (by simp)

theorem pointNormalChartInverse_at_point (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    pointNormalChartInverse g p B symmetric p = 0 := by
  have h := (pointNormalChartMap_analytic g p B).contDiffAt.localInverse_apply_image
    (pointNormalChartMap_hasFDerivAt g p B symmetric) (by simp)
  simpa only [pointNormalChartMap_zero] using h

theorem pointNormalChartInverse_analytic (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    ContDiffAt ℝ ⊤ (pointNormalChartInverse g p B symmetric) p := by
  have h := (pointNormalChartMap_analytic g p B).contDiffAt.to_localInverse
    (pointNormalChartMap_hasFDerivAt g p B symmetric) (by simp)
  simpa only [pointNormalChartMap_zero] using h

#print axioms metric_pullback_congr_map_eventually
#print axioms coordinate_derivative_of_frame_jacobian
#print axioms pointNormalChartMap_analytic
#print axioms pointNormalChartMap_hasFDerivAt
#print axioms pointNormalChartInverse_at_point
#print axioms pointNormalChartInverse_analytic
end
end AASCSemanticExhaustion
