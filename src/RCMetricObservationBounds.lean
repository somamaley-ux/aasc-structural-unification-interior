import RCDilationDomain

/-! Actual normalized-metric observations, with the same fixed-a domain.
The true pullback still has the separately proved epsilon^2 factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion AASCMetricConstruction
open AASCKleinGordon.CurvedKG AASCKleinGordon.SameActionSource
open scoped Topology BigOperators
namespace AASCKleinGordon.RecoveryComparison

theorem normalized_metric_quadratic_error (a : Parameters) (epsilon : ℝ) (y v : CoordinatePoint)
    (inside : epsilon • y ∈ sourceDomain a)
    (small : |conformalFrequency a*(epsilon • y) 0| ≤ (1:ℝ)/2) :
    |wickMatrixQuadratic (normalizedRescaledMetric a epsilon y) v-wickMatrixQuadratic metric v| ≤
      6*(conformalFrequency a*(epsilon • y) 0)^2*|wickMatrixQuadratic metric v| := by
  change |wickMatrixQuadratic (sourceMetric a (epsilon • y)) v-wickMatrixQuadratic metric v| ≤ _
  rw [source_metric_conformal]
  change |wickMatrixQuadratic (sourceFactor a (epsilon • y) • metric) v-wickMatrixQuadratic metric v| ≤ _
  rw [quadratic_scalar_multiple,
    show sourceFactor a (epsilon • y)*wickMatrixQuadratic metric v-wickMatrixQuadratic metric v =
      (sourceFactor a (epsilon • y)-1)*wickMatrixQuadratic metric v by ring,abs_mul]
  exact mul_le_mul_of_nonneg_right (protected_scale_error_bounds a _ inside small).2 (abs_nonneg _)

theorem source_origin_matches_constructed_sr_form (a : Parameters)
    (z : AASCKleinGordon.CanonicalLicensing.SRIntegration.SREvent) :
    comparisonQuadratic (sourceMetric a 0)
      (AASCKleinGordon.CanonicalLicensing.SRIntegration.srEventCoordinates z) =
      -AASCKleinGordon.CanonicalLicensing.SRIntegration.srOriginalOrderQuadratic z := by
  have zeroLeaf : centralLeafPoint (0 : KGSpatialSpace) = 0 := by simp [centralLeafPoint]
  have inside : (0 : KGSpatialSpace) ∈ centralLeafDomain (conformalFrequency a) := by
    change dist (0 : KGSpatialSpace) 0 < protectedRadius (conformalFrequency a)
    simpa only [dist_self] using protected_radius_positive (conformalFrequency a)
  have same := same_initial_metric a 0 inside
  rw [zeroLeaf] at same
  rw [same]
  exact AASCKleinGordon.CanonicalLicensing.SRIntegration.sr_source_derived_form_matches_actual_zero_eh_operand _ z

end AASCKleinGordon.RecoveryComparison
