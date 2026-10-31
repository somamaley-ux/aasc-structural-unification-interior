import PointNormalChartConstruction

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

theorem coordinateMetricPullback_identity (g : MetricField) :
    coordinateMetricPullback g (fun x => x) = g := by
  funext x
  have hj : coordinateJacobian (fun y : CoordinatePoint => y) x = 1 := by
    simpa using translation_coordinate_jacobian (0 : CoordinatePoint) x
  rw [coordinateMetricPullback_matrix, hj]
  simp

theorem affineCoordinateMap_origin_refl :
    affineCoordinateMap 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) = (fun x => x) := by
  funext x i
  simp [affineCoordinateMap, quadraticCoordinateMap, quadraticPolynomial]

theorem normalizingCoordinateMap_retraction (g : MetricField) (germ : NormalizedSmoothMetricGerm g) :
    normalizingCoordinateMap g = (fun x => x) := by
  funext x i
  simp [normalizingCoordinateMap, quadraticIdentityMap, quadraticCoordinateMap,
    normalCoordinateCorrection, normalized_metric_christoffel_zero g germ, quadraticPolynomial]

theorem pointNormalizedMetric_retraction (g : MetricField) (germ : NormalizedSmoothMetricGerm g) :
    pointNormalizedMetric g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) = g := by
  unfold pointNormalizedMetric framedMetricField
  rw [affineCoordinateMap_origin_refl, coordinateMetricPullback_identity,
    normalizingCoordinateMap_retraction g germ, coordinateMetricPullback_identity]

theorem normalizedMetric_identity_frame (g : MetricField) (germ : NormalizedSmoothMetricGerm g) :
    LorentzFrameAt g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) := by
  simp [LorentzFrameAt, coordinateFrameMatrix_refl, germ.2.2.1]

def normalChartCurvature (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (frame : LorentzFrameAt g p B) : curvatureSpace :=
  normalizedLeviCivitaCurvature (pointNormalizedMetric g p B)
    (pointNormalizedMetric_germ g p B symmetric smooth frame)

theorem normalChartCurvature_retraction (g : MetricField) (germ : NormalizedSmoothMetricGerm g) :
    normalChartCurvature g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) germ.1 germ.2.1
      (normalizedMetric_identity_frame g germ) = normalizedLeviCivitaCurvature g germ := by
  apply Subtype.ext
  change loweredConnectionCurvature _ (leviCivitaCoefficients _) 0 = _
  rw [pointNormalizedMetric_retraction g germ]
  rfl

/-- One unique coefficient triple for every smooth point and admitted Lorentz
frame in the coordinate-field envelope. Curvature is the actual connection
curvature in the constructed normal chart. Its transport to a general intrinsic
manifold/source interface is not hidden in this theorem. -/
theorem metric_response_normal_chart_envelope_exhaustion (E : MetricFieldResponse)
    (core : MetricFirstResponseCore E) :
    ∃! coefficients : ℝ × ℝ × ℝ,
      ∀ (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
        (symmetric : MetricFieldSymmetric g)
        (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (frame : LorentzFrameAt g p B),
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B =
        coefficients.1 • ricciResponse (normalChartCurvature g p B symmetric smooth frame) +
          coefficients.2.1 • scalarMetricResponse (normalChartCurvature g p B symmetric smooth frame) +
            coefficients.2.2 • metric := by
  obtain ⟨coefficients, h, unique⟩ := actual_normalized_metric_response_exhaustion E core
  refine ⟨coefficients, ?_, ?_⟩
  · intro g p B symmetric smooth frame
    have hc := h (pointNormalizedMetric g p B) (pointNormalizedMetric_germ g p B symmetric smooth frame)
    exact (natural_response_point_normal_chart E core.1 g p B symmetric).symm.trans hc
  · intro other ho
    apply unique other
    intro g germ
    have hh := ho g 0 (ContinuousLinearEquiv.refl ℝ CoordinatePoint) germ.1 germ.2.1
      (normalizedMetric_identity_frame g germ)
    simpa only [coordinateFrameMatrix_refl, Matrix.transpose_one, one_mul, mul_one,
      normalChartCurvature_retraction g germ] using hh

#print axioms coordinateMetricPullback_identity
#print axioms affineCoordinateMap_origin_refl
#print axioms normalizingCoordinateMap_retraction
#print axioms pointNormalizedMetric_retraction
#print axioms normalizedMetric_identity_frame
#print axioms normalChartCurvature_retraction
#print axioms metric_response_normal_chart_envelope_exhaustion
end
end AASCSemanticExhaustion
