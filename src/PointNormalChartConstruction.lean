import MetricNormalCoordinates
import CoordinatePullbackComposition
import NormalizedMetricLeviCivita

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def affineCoordinateMap (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :=
  quadraticCoordinateMap p B (fun _ => 0)

def framedMetricField (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : MetricField :=
  coordinateMetricPullback g (affineCoordinateMap p B)

def pointNormalizedMetric (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : MetricField :=
  coordinateMetricPullback (framedMetricField g p B) (normalizingCoordinateMap (framedMetricField g p B))

def pointNormalChartMap (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : CoordinatePoint → CoordinatePoint :=
  fun x => affineCoordinateMap p B (normalizingCoordinateMap (framedMetricField g p B) x)

def LorentzFrameAt (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : Prop :=
  (coordinateFrameMatrix B).transpose * g p * coordinateFrameMatrix B = metric

theorem affineCoordinateMap_smooth (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    ContDiff ℝ ⊤ (affineCoordinateMap p B) := quadraticCoordinateMap_smooth _ _ _

theorem affineCoordinateMap_zero (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    affineCoordinateMap p B 0 = p := quadraticCoordinateMap_zero _ _ _

theorem affineCoordinateMap_jacobian (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (x : CoordinatePoint) : coordinateJacobian (affineCoordinateMap p B) x = coordinateFrameMatrix B := by
  ext i a
  rw [affineCoordinateMap, quadraticCoordinateMap_jacobian _ _ _ (by simp)]
  simp [coordinateFrameMatrix]

theorem normalizingCoordinateMap_smooth (g : MetricField) :
    ContDiff ℝ ⊤ (normalizingCoordinateMap g) := quadraticCoordinateMap_smooth _ _ _

theorem framedMetricField_symmetric (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    MetricFieldSymmetric (framedMetricField g p B) := coordinateMetricPullback_symmetric g symmetric _

theorem framedMetricField_smoothAt (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) :
    ∀ a b, ContDiffAt ℝ ⊤ (fun x => framedMetricField g p B x a b) 0 := by
  intro a b
  apply coordinateMetricPullback_contDiffAt g (affineCoordinateMap p B) 0
    (affineCoordinateMap_smooth p B).contDiffAt
  simpa only [affineCoordinateMap_zero] using smooth

theorem framedMetricField_value (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (frame : LorentzFrameAt g p B) :
    framedMetricField g p B 0 = metric := by
  rw [framedMetricField, affineCoordinateMap, quadratic_metric_pullback_value _ _ _ _ (by simp)]
  exact frame

theorem pointNormalizedMetric_germ (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g)
    (smooth : ∀ a b, ContDiffAt ℝ ⊤ (fun x => g x a b) p) (frame : LorentzFrameAt g p B) :
    NormalizedSmoothMetricGerm (pointNormalizedMetric g p B) :=
  normalizing_metric_germ (framedMetricField g p B) (framedMetricField_symmetric g p B symmetric)
    (framedMetricField_smoothAt g p B smooth) (framedMetricField_value g p B frame)

theorem pointNormalChartMap_local (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : SmoothCoordinateAt (pointNormalChartMap g p B) 0 := by
  unfold pointNormalChartMap
  apply smoothCoordinateAt_comp (affineCoordinateMap p B)
    (normalizingCoordinateMap (framedMetricField g p B)) 0
  · simpa only [normalizingCoordinateMap_zero] using quadraticCoordinateMap_local_chart p B (fun _ => 0)
  · exact normalizingCoordinateMap_local_chart _

theorem pointNormalChartMap_zero (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : pointNormalChartMap g p B 0 = p := by
  simp [pointNormalChartMap, normalizingCoordinateMap_zero, affineCoordinateMap_zero]

theorem pointNormalChartMap_jacobian (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (symmetric : MetricFieldSymmetric g) :
    coordinateJacobian (pointNormalChartMap g p B) 0 = coordinateFrameMatrix B := by
  unfold pointNormalChartMap
  rw [coordinateJacobian_comp _ _ 0
    ((affineCoordinateMap_smooth p B).differentiable (by simp) _)
    ((normalizingCoordinateMap_smooth _).differentiable (by simp) 0),
    affineCoordinateMap_jacobian,
    normalizingCoordinateMap_jacobian _ (framedMetricField_symmetric g p B symmetric), mul_one]

theorem pointNormalChartMap_pullback (g : MetricField) (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) :
    coordinateMetricPullback g (pointNormalChartMap g p B) = pointNormalizedMetric g p B :=
  (coordinateMetricPullback_comp g _ _ (affineCoordinateMap_smooth p B)
    (normalizingCoordinateMap_smooth (framedMetricField g p B))).symm

theorem natural_response_point_normal_chart (E : MetricFieldResponse) (natural : MetricResponseNatural E)
    (g : MetricField) (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (symmetric : MetricFieldSymmetric g) :
    E (pointNormalizedMetric g p B) 0 =
      (coordinateFrameMatrix B).transpose * E g p * coordinateFrameMatrix B := by
  have h := natural (pointNormalChartMap g p B) 0 (pointNormalChartMap_local g p B) g
  simpa only [pointNormalChartMap_pullback, pointNormalChartMap_zero,
    pointNormalChartMap_jacobian g p B symmetric] using h

#print axioms affineCoordinateMap_smooth
#print axioms affineCoordinateMap_zero
#print axioms affineCoordinateMap_jacobian
#print axioms normalizingCoordinateMap_smooth
#print axioms framedMetricField_symmetric
#print axioms framedMetricField_smoothAt
#print axioms framedMetricField_value
#print axioms pointNormalizedMetric_germ
#print axioms pointNormalChartMap_local
#print axioms pointNormalChartMap_zero
#print axioms pointNormalChartMap_jacobian
#print axioms pointNormalChartMap_pullback
#print axioms natural_response_point_normal_chart
end
end AASCSemanticExhaustion
