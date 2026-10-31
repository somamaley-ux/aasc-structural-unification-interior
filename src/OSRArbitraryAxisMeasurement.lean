import OSRRotatedMeasurement

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def axisBoost (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (t r : ℝ) (hyper : t^2-r^2=1) : SRMatrixFrame :=
  srRestCoordinateUnit Q*srUnitAxialBoost t r hyper*(srRestCoordinateUnit Q)⁻¹

theorem axis_boost_actually_admitted (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t) :
    axisBoost Q t r hyper ∈ srNativeFrameComparisons :=
  srNativeFrameComparisons.mul_mem (rotated_boost_is_actually_admitted Q proper t r hyper positive)
    (srNativeFrameComparisons.inv_mem (proper_spatial_rotation_actually_supplied Q proper))

theorem actual_inverse_rotation_event (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (z : SREvent) :
    srMatrixFrameEventLinear (srRestCoordinateUnit Q)⁻¹ z=(z.1,Q.symm z.2) := by
  have inverse := sr_event_frame_inverse_left (srRestCoordinateUnit Q) (z.1,Q.symm z.2)
  simpa only [sr_original_rest_frame_event_value,Q.apply_symm_apply] using inverse

theorem actual_axis_boost_time (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (t r : ℝ) (hyper : t^2-r^2=1) (b z : SREvent) :
    (frameEvent (axisBoost Q t r hyper) b z).1=t*z.1+r*(Q.symm z.2) 0+b.1 := by
  simp only [axisBoost,frameEvent,sr_event_frame_mul,actual_inverse_rotation_event,
    sr_original_rest_frame_event_value,sr_unit_axial_boost_time,Prod.fst_add]

theorem actual_axis_selected_rest_time (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X : SRSpace) :
    selectedSiteTime (axisBoost Q t r hyper) b T X=selectedRestTime t r b T (Q.symm X) := by
  have chosen := (measuring_frame_selected_events_actual_and_unique (axisBoost Q t r hyper)
    (axis_boost_actually_admitted Q proper t r hyper positive) b T X).1
  change (frameEvent (axisBoost Q t r hyper) b (_,X)).1=T at chosen
  rw [actual_axis_boost_time] at chosen
  unfold selectedRestTime
  apply (eq_div_iff positive.ne').mpr
  linarith

theorem arbitrary_axis_actual_measured_length (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    ‖(measuredEndpoint (axisBoost Q t r hyper) b T Y).2-(measuredEndpoint (axisBoost Q t r hyper) b T X).2‖^2=
      ((Q.symm Y) 0-(Q.symm X) 0)^2/t^2+
      ((Q.symm Y) 1-(Q.symm X) 1)^2+((Q.symm Y) 2-(Q.symm X) 2)^2 := by
  rw [general_measuring_separation_is_actual_source_form _ (axis_boost_actually_admitted Q proper t r hyper positive),
    actual_axis_selected_rest_time Q proper t r hyper positive,actual_axis_selected_rest_time Q proper t r hyper positive,
    (actual_selected_endpoint_separation t r hyper positive b T (Q.symm X) (Q.symm Y)).2.2.2]
  have norms : ‖Y-X‖^2=‖Q.symm Y-Q.symm X‖^2 := by rw [←map_sub,Q.symm.norm_map]
  rw [norms,EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_succ,Real.norm_eq_abs,PiLp.sub_apply]
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*((Q.symm Y) 0-(Q.symm X) 0)^2) hyper]

theorem arbitrary_axis_actual_selected_time_gap (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    selectedSiteTime (axisBoost Q t r hyper) b T Y-selectedSiteTime (axisBoost Q t r hyper) b T X=
      -(r/t)*((Q.symm Y) 0-(Q.symm X) 0) := by
  rw [actual_axis_selected_rest_time Q proper t r hyper positive,actual_axis_selected_rest_time Q proper t r hyper positive]
  exact (actual_selected_endpoint_separation t r hyper positive b T (Q.symm X) (Q.symm Y)).2.2.2

end AASCKleinGordon.OperationalSR
