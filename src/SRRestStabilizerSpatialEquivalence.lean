import SROriginalSpatialFrameAlignment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion

theorem sr_rest_stabilizer_event_quadratic (R : SRMatrixFrame)
    (role : srIsOriginalProperRestRotation R) (z : SREvent) :
    (srMatrixFrameEventLinear R z).1^2 - ‖(srMatrixFrameEventLinear R z).2‖^2 = z.1^2-‖z.2‖^2 := by
  change (srMatrixFrameEvent R z).1^2 - ‖(srMatrixFrameEvent R z).2‖^2 = _
  rw [← sr_coordinate_unit_quadratic_is_source_form,sr_event_frame_coordinate_square,
    ← sr_frame_pullback_quadratic,role.1,sr_coordinate_unit_quadratic_is_source_form]

theorem sr_rest_stabilizer_fixes_actual_rest_vector (R : SRMatrixFrame)
    (role : srIsOriginalProperRestRotation R) : srMatrixFrameEventLinear R (1,0) = (1,0) := by
  apply srEventCoordinates.injective
  change srEventCoordinates (srMatrixFrameEvent R (1,0)) = srEventCoordinates (1,0)
  rw [sr_event_frame_coordinate_square]
  change (R : ComparisonMatrix).mulVec (originalComparisonProbe 0) = originalComparisonProbe 0
  exact role.2.1

theorem sr_rest_stabilizer_preserves_original_time (R : SRMatrixFrame)
    (role : srIsOriginalProperRestRotation R) (z : SREvent) :
    (srMatrixFrameEventLinear R z).1 = z.1 := by
  have h0 := sr_rest_stabilizer_event_quadratic R role z
  have h1 := sr_rest_stabilizer_event_quadratic R role ((1,0)+z)
  have add : srMatrixFrameEventLinear R ((1,0)+z) = (1,0)+srMatrixFrameEventLinear R z := by
    rw [map_add,sr_rest_stabilizer_fixes_actual_rest_vector R role]
  rw [add] at h1
  simp only [Prod.fst_add,Prod.snd_add,zero_add] at h1
  nlinarith

def srRestStabilizerSpatialLinear (R : SRMatrixFrame) : SRSpace →ₗ[ℝ] SRSpace :=
  (LinearMap.snd ℝ ℝ SRSpace).comp
    ((srMatrixFrameEventLinear R).toLinearMap.comp (LinearMap.inr ℝ ℝ SRSpace))

theorem sr_rest_stabilizer_spatial_bijective (R : SRMatrixFrame)
    (role : srIsOriginalProperRestRotation R) : Function.Bijective (srRestStabilizerSpatialLinear R) := by
  constructor
  · intro x y same
    have pair : srMatrixFrameEventLinear R (0,x) = srMatrixFrameEventLinear R (0,y) := by
      apply Prod.ext
      · rw [sr_rest_stabilizer_preserves_original_time R role,
          sr_rest_stabilizer_preserves_original_time R role]
      · exact same
    exact congrArg Prod.snd ((srMatrixFrameEventLinear R).injective pair)
  · intro y
    obtain ⟨z,hz⟩ := (srMatrixFrameEventLinear R).surjective (0,y)
    have time : z.1 = 0 := (sr_rest_stabilizer_preserves_original_time R role z).symm.trans
      (congrArg Prod.fst hz)
    refine ⟨z.2,?_⟩
    have pair : (0,z.2) = z := Prod.ext time.symm rfl
    change (srMatrixFrameEventLinear R (0,z.2)).2 = y
    rw [pair,hz]

def srRestStabilizerSpatialIsometry (R : SRMatrixFrame)
    (role : srIsOriginalProperRestRotation R) : SRSpace ≃ₗᵢ[ℝ] SRSpace :=
  {LinearEquiv.ofBijective (srRestStabilizerSpatialLinear R)
      (sr_rest_stabilizer_spatial_bijective R role) with
    norm_map' := by
      intro x
      have h := sr_rest_stabilizer_event_quadratic R role (0,x)
      rw [sr_rest_stabilizer_preserves_original_time R role] at h
      change ‖srRestStabilizerSpatialLinear R x‖ = ‖x‖
      change (0:ℝ)^2 - ‖srRestStabilizerSpatialLinear R x‖^2 = 0^2-‖x‖^2 at h
      nlinarith [norm_nonneg (srRestStabilizerSpatialLinear R x),norm_nonneg x]}

theorem sr_rest_stabilizer_is_embedded_spatial_isometry (R : SRMatrixFrame)
    (role : srIsOriginalProperRestRotation R) :
    srRestCoordinateUnit (srRestStabilizerSpatialIsometry R role) = R := by
  have split (z : SREvent) : srMatrixFrameEventLinear R z =
      (z.1,srRestStabilizerSpatialIsometry R role z.2) := by
    apply Prod.ext
    · exact sr_rest_stabilizer_preserves_original_time R role z
    · have decomposition : z = z.1 • (1,0) + (0,z.2) := by ext <;> simp
      conv_lhs => rw [decomposition,map_add,map_smul,sr_rest_stabilizer_fixes_actual_rest_vector R role]
      change (z.1 • (1,0) + srMatrixFrameEventLinear R (0,z.2)).2 = _
      simp only [Prod.snd_add,Prod.smul_snd,smul_zero,zero_add]
      rfl
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (srRestCoordinateUnit (srRestStabilizerSpatialIsometry R role) : ComparisonMatrix).mulVec v =
    (R : ComparisonMatrix).mulVec v
  rw [sr_rest_coordinate_unit_apply]
  have h := sr_event_frame_coordinate_square R (srEventCoordinates.symm v)
  rw [srEventCoordinates.apply_symm_apply] at h
  rw [← h]
  exact congrArg srEventCoordinates (split _).symm

theorem sr_original_rest_role_iff_spatial_so3 (R : SRMatrixFrame) :
    srIsOriginalProperRestRotation R ↔
      ∃ Q : SRSpace ≃ₗᵢ[ℝ] SRSpace, LinearMap.det Q.toLinearMap = 1 ∧ srRestCoordinateUnit Q = R := by
  constructor
  · intro role
    let Q := srRestStabilizerSpatialIsometry R role
    have same : srRestCoordinateUnit Q = R := sr_rest_stabilizer_is_embedded_spatial_isometry R role
    have determinant : (R : ComparisonMatrix).det = 1 := by
      have h := congrArg Matrix.det role.1
      simp only [srFramePullback,Matrix.det_mul,Matrix.det_transpose,comparison_unit_lorentz_det] at h
      nlinarith [role.2.2]
    refine ⟨Q,?_,same⟩
    rw [← sr_original_spatial_frame_coordinate_determinant Q,same,determinant]
  · rintro ⟨Q,proper,rfl⟩
    exact sr_original_spatial_frame_has_exact_rest_role Q proper

#print axioms sr_original_rest_role_iff_spatial_so3
end AASCKleinGordon.CanonicalLicensing.SRIntegration
