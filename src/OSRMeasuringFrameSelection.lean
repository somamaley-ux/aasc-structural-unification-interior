import OSRInertialMeasurements

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def observerSlope (A : SRMatrixFrame) : ℝ := (srMatrixFrameEventLinear A restUnit).1

def selectedSiteTime (A : SRMatrixFrame) (b : SREvent) (T : ℝ) (X : SRSpace) : ℝ :=
  (T-(frameEvent A b (0,X)).1)/observerSlope A

def measuredEndpoint (A : SRMatrixFrame) (b : SREvent) (T : ℝ) (X : SRSpace) : SREvent :=
  frameEvent A b (selectedSiteTime A b T X,X)

theorem observer_slope_actually_positive (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons) :
    0 < observerSlope A := (native_frame_preserves_unit A admitted restUnit restUnit_future).1

theorem actual_site_event_affine_time (A : SRMatrixFrame) (b : SREvent) (u : ℝ) (X : SRSpace) :
    (frameEvent A b (u,X)).1=(frameEvent A b (0,X)).1+u*observerSlope A := by
  have decompose : ((u,X):SREvent)=(0,X)+u • restUnit := by simp [restUnit]
  rw [frameEvent,decompose,map_add,map_smul]
  simp only [frameEvent,Prod.fst_add,Prod.smul_fst,smul_eq_mul,observerSlope]
  ring

theorem measuring_frame_selected_events_actual_and_unique (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) (b : SREvent) (T : ℝ) (X : SRSpace) :
    (measuredEndpoint A b T X).1=T ∧
    ∀ u : ℝ, (frameEvent A b (u,X)).1=T → u=selectedSiteTime A b T X := by
  have positive := observer_slope_actually_positive A admitted
  constructor
  · unfold measuredEndpoint
    rw [actual_site_event_affine_time]
    unfold selectedSiteTime
    field_simp
    ring
  · intro u same
    rw [actual_site_event_affine_time] at same
    apply (eq_div_iff positive.ne').mpr
    linarith

theorem general_selection_is_actual_axial_selection (t r : ℝ) (hyper : t^2-r^2=1)
    (positive : 0 < t) (b : SREvent) (T : ℝ) (X : SRSpace) :
    measuredEndpoint (srUnitAxialBoost t r hyper) b T X=selectedEndpoint t r hyper b T X := by
  have selected := (endpoint_selection_is_simultaneous_and_unique t r hyper positive b T X).1
  have unique := (measuring_frame_selected_events_actual_and_unique (srUnitAxialBoost t r hyper)
    (sr_all_future_unit_axial_boosts_are_actually_supplied t r hyper positive) b T X).2
  have times := unique (selectedRestTime t r b T X) selected
  unfold measuredEndpoint selectedEndpoint
  rw [times]

end AASCKleinGordon.OperationalSR
