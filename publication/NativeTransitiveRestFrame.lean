import SRCalibratedFrameTheorem
import TransitiveRestRotations

/-! The spatial rest group is extracted from the admitted frame comparisons.
Its frontier transitivity is the physical input replacing a list of rotations. -/
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
noncomputable section
set_option autoImplicit false
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCInertial.RestRotations
open scoped Matrix

private noncomputable def spatialFrame : (SRSpace ≃ₗᵢ[ℝ] SRSpace) →* SRMatrixFrame where
  toFun := srRestCoordinateUnit
  map_one' := by
    apply Units.ext
    apply Matrix.mulVec_injective
    funext v
    rw [sr_rest_coordinate_unit_apply]
    change srEventCoordinates (srEventCoordinates.symm v) = _
    simp
  map_mul' Q R := by
    apply Units.ext
    apply Matrix.mulVec_injective
    funext v
    change _ = ((srRestCoordinateUnit Q : ComparisonMatrix) *
      (srRestCoordinateUnit R : ComparisonMatrix)).mulVec v
    rw [← Matrix.mulVec_mulVec, sr_rest_coordinate_unit_apply,
      sr_rest_coordinate_unit_apply, sr_rest_coordinate_unit_apply,
      srEventCoordinates.symm_apply_apply]
    rfl

private def spatialDet : (SRSpace ≃ₗᵢ[ℝ] SRSpace) →* ℝ where
  toFun Q := LinearMap.det Q.toLinearMap
  map_one' := LinearMap.det_id
  map_mul' Q R := LinearMap.det_comp Q.toLinearMap R.toLinearMap

/-- Proper rest rotations whose actual frame representations are admitted. -/
def srAdmittedProperSpatialRest (frames : Subgroup SRMatrixFrame) :
    Subgroup (SRSpace ≃ₗᵢ[ℝ] SRSpace) :=
  spatialDet.ker ⊓ frames.comap spatialFrame

theorem sr_mem_admitted_proper_spatial_rest (frames : Subgroup SRMatrixFrame)
    (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) :
    Q ∈ srAdmittedProperSpatialRest frames ↔
      LinearMap.det Q.toLinearMap = 1 ∧ srRestCoordinateUnit Q ∈ frames := Iff.rfl

/-- Transitivity of the *admitted* proper rest comparisons gives every
proper rest matrix in the native frame group (spatial dimension three). -/
theorem sr_transitive_rest_supplies_original_rest_family (frames : Subgroup SRMatrixFrame)
    (transitive : FrontierTransitive (srAdmittedProperSpatialRest frames))
    (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (oriented : LinearMap.det Q.toLinearMap = 1) :
    srRestCoordinateUnit Q ∈ frames := by
  let H := srAdmittedProperSpatialRest frames
  have proper (R : SRSpace ≃ₗᵢ[ℝ] SRSpace) (hR : R ∈ H) : determinant R = 1 :=
    ((sr_mem_admitted_proper_spatial_rest frames R).mp hR).1
  have supplied : Q ∈ H :=
    (proper_rotations_of_transitive_frontier H (by simp [SRSpace]) proper transitive Q).mpr oriented
  exact ((sr_mem_admitted_proper_spatial_rest frames Q).mp supplied).2

/-- The interval is calibrated for every admitted native frame. The
physical rotation hypothesis concerns which admitted rest comparisons
relate frontier points. Full rotation supply is a derived intermediate. -/
theorem sr_transitive_rest_and_same_tick_preserve_native_interval
    (μ0 : ℝ) (mass : 0 < μ0) (frames : Subgroup SRMatrixFrame)
    (T : ℝ) (positive : 0 < T)
    (cone : ∀ A ∈ frames, srMatrixFrameEvent A '' srRayFutureCone = srRayFutureCone)
    (orient : ∀ A ∈ frames, 0 < (A : ComparisonMatrix).det)
    (transitive : FrontierTransitive (srAdmittedProperSpatialRest frames))
    (sameTick : ∀ d : ℝ, ∀ hd : 0 < d, srDilationUnit d hd.ne' ∈ frames →
      d*T = srNativeClockActualInterval μ0 (srOriginalRestTickUse μ0 T))
    (A : SRMatrixFrame) (admitted : A ∈ frames) (z : SREvent) :
    srOriginalOrderQuadratic (srMatrixFrameEvent A z) = srOriginalOrderQuadratic z := by
  let source : SRCalibratedFrameSource μ0 := {
    comparisons := frames
    tickSpan := T
    tickPositive := positive
    coneReceipt := cone
    orientation := orient
    originalRestFamily := sr_transitive_rest_supplies_original_rest_family frames transitive
    sameOriginalRestTick := sameTick }
  exact sr_admitted_frames_preserve_same_source_derived_form μ0 mass source A admitted z

end
end AASCKleinGordon.CanonicalLicensing.SRIntegration
