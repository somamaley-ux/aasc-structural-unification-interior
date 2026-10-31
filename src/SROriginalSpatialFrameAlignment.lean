import SRFrameConeRigidity
import SRAlignedFrameScaleRemoval

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open scoped Matrix BigOperators

def srRestCoordinateLinear (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) : CoordinatePoint ≃ₗ[ℝ] CoordinatePoint :=
  (srEventCoordinates.symm.trans (srRayRestComparison Q).toLinearEquiv).trans srEventCoordinates

def srRestCoordinateUnit (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) : SRMatrixFrame :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (srRestCoordinateLinear Q))

theorem sr_rest_coordinate_unit_matrix (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) :
    (srRestCoordinateUnit Q : ComparisonMatrix) =
      LinearMap.toMatrix' (srRestCoordinateLinear Q).toLinearMap := rfl

theorem sr_rest_coordinate_unit_apply (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (v : CoordinatePoint) :
    (srRestCoordinateUnit Q : ComparisonMatrix).mulVec v =
      srEventCoordinates ((srEventCoordinates.symm v).1,Q (srEventCoordinates.symm v).2) := by
  rw [sr_rest_coordinate_unit_matrix,LinearMap.toMatrix'_mulVec]
  rfl

theorem sr_original_spatial_frame_coordinate_determinant (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) :
    (srRestCoordinateUnit Q : ComparisonMatrix).det = LinearMap.det Q.toLinearMap := by
  rw [sr_rest_coordinate_unit_matrix,LinearMap.det_toMatrix']
  change LinearMap.det (srEventCoordinates.toLinearMap.comp
    ((srRayRestComparison Q).toLinearMap.comp srEventCoordinates.symm.toLinearMap)) = _
  rw [LinearMap.det_conj]
  change LinearMap.det (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) Q.toLinearMap) = _
  rw [LinearMap.det_prodMap,LinearMap.det_id,one_mul]

theorem sr_original_spatial_frame_preserves_constructed_quadratic
    (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (v : CoordinatePoint) :
    comparisonQuadratic comparisonUnitLorentz ((srRestCoordinateUnit Q : ComparisonMatrix).mulVec v) =
      comparisonQuadratic comparisonUnitLorentz v := by
  rw [sr_rest_coordinate_unit_apply,sr_coordinate_unit_quadratic_is_source_form]
  have original := sr_coordinate_unit_quadratic_is_source_form (srEventCoordinates.symm v)
  rw [srEventCoordinates.apply_symm_apply] at original
  rw [original]
  simp

theorem sr_original_spatial_frame_has_exact_rest_role
    (Q : SRSpace ≃ₗᵢ[ℝ] SRSpace) (proper : LinearMap.det Q.toLinearMap = 1) :
    srIsOriginalProperRestRotation (srRestCoordinateUnit Q) := by
  refine ⟨?_,?_,?_⟩
  · apply (original_comparison_answers_separate_symmetric_receipts _ _
      (sr_frame_pullback_symmetric _) sr_comparison_unit_lorentz_symmetric).mp
    funext i
    exact (sr_frame_pullback_quadratic _ _).trans
      (sr_original_spatial_frame_preserves_constructed_quadratic Q _)
  · rw [sr_rest_coordinate_unit_apply]
    have initial : srEventCoordinates.symm (originalComparisonProbe 0) = (1,0) := by
      apply srEventCoordinates.injective
      rw [srEventCoordinates.apply_symm_apply]
      rfl
    rw [initial,map_zero]
    rfl
  · rw [sr_original_spatial_frame_coordinate_determinant,proper]
    norm_num

def srFirstSpatialUnit : SRSpace := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![1,0,0]

theorem sr_first_spatial_unit_norm : ‖srFirstSpatialUnit‖ = 1 := by
  have h : ‖srFirstSpatialUnit‖^2 = (1 : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [srFirstSpatialUnit,Fin.sum_univ_succ]
  nlinarith [norm_nonneg srFirstSpatialUnit]

theorem sr_actual_original_spatial_rotations_align_every_frame_column
    (G : Subgroup SRMatrixFrame)
    (allOriginalRest : ∀ R : SRMatrixFrame, srIsOriginalProperRestRotation R → R ∈ G)
    (A : SRMatrixFrame) :
    ∃ S : SRMatrixFrame, S ∈ G ∧
      srFramePullback (S : ComparisonMatrix) = comparisonUnitLorentz ∧
      0 < (S : ComparisonMatrix).det ∧
      ∃ t r : ℝ, ((S*A : SRMatrixFrame) : ComparisonMatrix).mulVec (originalComparisonProbe 0) =
        ![t,r,0,0] := by
  let z := srEventCoordinates.symm ((A : ComparisonMatrix).mulVec (originalComparisonProbe 0))
  have norms : ‖z.2‖ = ‖‖z.2‖ • srFirstSpatialUnit‖ := by
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _),sr_first_spatial_unit_norm,mul_one]
  obtain ⟨Q,proper,aligned⟩ := sr_equal_length_vectors_related_by_orientation_preserving_isometry
    (by simp : 2 ≤ Module.finrank ℝ SRSpace) z.2 (‖z.2‖ • srFirstSpatialUnit) norms
  let S := srRestCoordinateUnit Q
  have role := sr_original_spatial_frame_has_exact_rest_role Q proper
  refine ⟨S,allOriginalRest S role,role.1,role.2.2,z.1,‖z.2‖,?_⟩
  change ((S : ComparisonMatrix)*(A : ComparisonMatrix)).mulVec (originalComparisonProbe 0) = _
  rw [← Matrix.mulVec_mulVec,sr_rest_coordinate_unit_apply]
  change srEventCoordinates (z.1,Q z.2) = _
  rw [aligned]
  ext i
  fin_cases i <;> simp [srEventCoordinates,srFirstSpatialUnit]

#print axioms sr_actual_original_spatial_rotations_align_every_frame_column
end AASCKleinGordon.CanonicalLicensing.SRIntegration
