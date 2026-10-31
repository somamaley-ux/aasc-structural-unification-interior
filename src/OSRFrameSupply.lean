import SRNativeMovingFrameSupply
import SRRestStabilizerSpatialEquivalence

/-! Actual arbitrary-direction frame supply, downstream of the constructed
source form and the existing native comparison family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
open scoped Matrix BigOperators
namespace AASCKleinGordon.OperationalSR

def IsFutureUnit (U : SREvent) : Prop :=
  0 < U.1 ∧ srOriginalOrderQuadratic U = 1

def IsFutureTimelike (w : SREvent) : Prop :=
  0 < w.1 ∧ 0 < srOriginalOrderQuadratic w

theorem axial_boost_rest_vector (t r : ℝ) (hyperbolic : t^2-r^2=1) :
    srMatrixFrameEventLinear (srUnitAxialBoost t r hyperbolic) (1,0) =
      (t,r • srFirstSpatialUnit) := by
  apply srEventCoordinates.injective
  change srEventCoordinates (srMatrixFrameEvent (srUnitAxialBoost t r hyperbolic) (1,0)) = _
  rw [sr_event_frame_coordinate_square]
  ext i
  fin_cases i <;>
    norm_num [srEventCoordinates,srUnitAxialBoost,srScaledAxialBoostUnit,srScaledAxialBoost,
      srFirstSpatialUnit,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  exact Or.inr rfl

theorem proper_spatial_rotation_actually_supplied (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace)
    (proper : LinearMap.det Q.toLinearMap = 1) : srRestCoordinateUnit Q ∈ srNativeFrameComparisons := by
  have role := sr_original_spatial_frame_has_exact_rest_role Q proper
  exact ⟨role.1,role.2.2,sr_native_rest_frames_preserve_original_cone Q⟩

theorem actual_native_future_unit_frame_supply (U : SREvent) (unit : IsFutureUnit U) :
    ∃ A : SRMatrixFrame, A ∈ srNativeFrameComparisons ∧
      srMatrixFrameEventLinear A (1,0) = U := by
  have hyperbolic : U.1^2-‖U.2‖^2=1 := by
    rw [←sr_original_order_quadratic_computed]
    exact unit.2
  have norms : ‖‖U.2‖ • srFirstSpatialUnit‖ = ‖U.2‖ := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),sr_first_spatial_unit_norm,mul_one]
  obtain ⟨Q,proper,aligned⟩ := sr_equal_length_vectors_related_by_orientation_preserving_isometry
    (by simp : 2 ≤ Module.finrank ℝ SRSpace) (‖U.2‖ • srFirstSpatialUnit) U.2 norms
  let B := srUnitAxialBoost U.1 ‖U.2‖ hyperbolic
  let R := srRestCoordinateUnit Q
  refine ⟨R*B,srNativeFrameComparisons.mul_mem
    (proper_spatial_rotation_actually_supplied Q proper)
    (sr_all_future_unit_axial_boosts_are_actually_supplied U.1 ‖U.2‖ hyperbolic unit.1),?_⟩
  rw [sr_event_frame_mul]
  change srMatrixFrameEventLinear (srRestCoordinateUnit Q)
    (srMatrixFrameEventLinear (srUnitAxialBoost U.1 ‖U.2‖ hyperbolic) (1,0)) = U
  rw [axial_boost_rest_vector,sr_original_rest_frame_event_value,aligned]

def suppliedUnitFrame (U : SREvent) (unit : IsFutureUnit U) : SRMatrixFrame :=
  Classical.choose (actual_native_future_unit_frame_supply U unit)

theorem supplied_unit_frame_mem (U : SREvent) (unit : IsFutureUnit U) :
    suppliedUnitFrame U unit ∈ srNativeFrameComparisons :=
  (Classical.choose_spec (actual_native_future_unit_frame_supply U unit)).1

theorem supplied_unit_frame_rest (U : SREvent) (unit : IsFutureUnit U) :
    srMatrixFrameEventLinear (suppliedUnitFrame U unit) (1,0) = U :=
  (Classical.choose_spec (actual_native_future_unit_frame_supply U unit)).2

end AASCKleinGordon.OperationalSR
