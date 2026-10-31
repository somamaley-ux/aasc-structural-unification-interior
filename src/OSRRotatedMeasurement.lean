import OSRNetworkSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR
open KGQuantum W9 TopologicalSpace AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

 theorem rotated_boost_is_actually_admitted (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t) :
    srRestCoordinateUnit Q*srUnitAxialBoost t r hyper ∈ srNativeFrameComparisons :=
  srNativeFrameComparisons.mul_mem (proper_spatial_rotation_actually_supplied Q proper)
    (sr_all_future_unit_axial_boosts_are_actually_supplied t r hyper positive)

theorem rotated_boost_actual_time (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (t r : ℝ) (hyper : t^2-r^2=1) (b z : SREvent) :
    (frameEvent (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b z).1=
      (frameEvent (srUnitAxialBoost t r hyper) b z).1 := by
  simp only [frameEvent,sr_event_frame_mul,sr_original_rest_frame_event_value,Prod.fst_add]

theorem rotated_measuring_time_is_actual_selected_time (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X : SRSpace) :
    measuringSiteTime ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ X=selectedRestTime t r b T X := by
  have chosen := measured_endpoint_lies_on_retained_hyperplane
    ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩
    (rotated_boost_is_actually_admitted Q proper t r hyper positive) X
  change (frameEvent (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b (_,X)).1=T at chosen
  rw [rotated_boost_actual_time] at chosen
  exact (endpoint_selection_is_simultaneous_and_unique t r hyper positive b T X).2 _ chosen

theorem general_measuring_separation_is_actual_source_form (A : SRMatrixFrame)
    (admitted : A ∈ srNativeFrameComparisons) (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    ‖(measuredEndpoint A b T Y).2-(measuredEndpoint A b T X).2‖^2=
      ‖Y-X‖^2-(selectedSiteTime A b T Y-selectedSiteTime A b T X)^2 := by
  have timeX := (measuring_frame_selected_events_actual_and_unique A admitted b T X).1
  have timeY := (measuring_frame_selected_events_actual_and_unique A admitted b T Y).1
  have same := frame_preserves_actual_source_form A admitted b
    (selectedSiteTime A b T X,X) (selectedSiteTime A b T Y,Y)
  change srOriginalOrderQuadratic (measuredEndpoint A b T Y-measuredEndpoint A b T X)=_ at same
  rw [sr_original_order_quadratic_computed,sr_original_order_quadratic_computed] at same
  simp only [Prod.fst_sub,Prod.snd_sub,timeX,timeY,sub_self] at same
  norm_num at same
  linarith

theorem rotated_actual_selected_length_squared (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (X Y : SRSpace) :
    ‖(measuredEndpoint (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b T Y).2-
      (measuredEndpoint (srRestCoordinateUnit Q*srUnitAxialBoost t r hyper) b T X).2‖^2=
      (Y 0-X 0)^2/t^2+(Y 1-X 1)^2+(Y 2-X 2)^2 := by
  rw [general_measuring_separation_is_actual_source_form _ (rotated_boost_is_actually_admitted Q proper t r hyper positive)]
  have tx := rotated_measuring_time_is_actual_selected_time Q proper t r hyper positive b T X
  have ty := rotated_measuring_time_is_actual_selected_time Q proper t r hyper positive b T Y
  change selectedSiteTime _ _ _ _=_ at tx ty
  rw [tx,ty,(actual_selected_endpoint_separation t r hyper positive b T X Y).2.2.2]
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_succ,Real.norm_eq_abs,PiLp.sub_apply]
  field_simp
  nlinarith [congrArg (fun z : ℝ => z*(Y 0-X 0)^2) hyper]

theorem successful_rotated_ruler_is_actual_measurement (a : Parameters) (s : ℝ) (Omega : Opens CoordinatePoint)
    (n : ℕ) (d : NetworkData a s Omega n) (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap=1) (t r : ℝ) (hyper : t^2-r^2=1) (positive : 0 < t)
    (b : SREvent) (T : ℝ) (i j : Fin (n+1))
    (domain : measuringDomain a s Omega n d ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ i j) :
    ∃ answer : MeasuringAnswer,
      measuringRead a s Omega n d ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ i j=some answer ∧
      answer.length^2=(d.sites.position j 0-d.sites.position i 0)^2/t^2+
        (d.sites.position j 1-d.sites.position i 1)^2+(d.sites.position j 2-d.sites.position i 2)^2 := by
  refine ⟨actualMeasuringAnswer a s Omega n d ⟨srRestCoordinateUnit Q*srUnitAxialBoost t r hyper,b,T⟩ i j,?_,?_⟩
  · simp [measuringRead,domain]
  · exact rotated_actual_selected_length_squared Q proper t r hyper positive b T _ _

end AASCKleinGordon.OperationalSR
