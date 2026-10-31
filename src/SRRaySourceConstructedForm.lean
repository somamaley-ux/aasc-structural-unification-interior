import SROccupiedIsotropicRaySource

/-! Apply the covariance/isotropy constructor to the inhabited calibrated
ray source, and prove that it actually computes the SR form on all vectors.
This is an application of the constructor, not only a nonempty input record. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def srRaySpatialNormQuadratic : QuadraticForm ℝ (SRClockSpatialSpace (srRayClock (E:=E))):=
  (LinearMap.BilinMap.toQuadraticMap (innerₗ (F:=E))).comp srRaySpatialEquiv.toLinearMap

theorem sr_ray_spatial_norm_quadratic_value (x : SRClockSpatialSpace (srRayClock (E:=E))) :
    srRaySpatialNormQuadratic x=‖(x:ℝ × E).2‖^2 := by
  change inner ℝ (x:ℝ × E).2 (x:ℝ × E).2=‖(x:ℝ × E).2‖^2
  exact real_inner_self_eq_norm_sq _

theorem sr_covariance_constructor_computes_the_original_ray_spatial_form :
    srSourceSpatialForm (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E))
      (srOccupiedIsotropicRaySource (E:=E))=srRaySpatialNormQuadratic (E:=E) := by
  have hp:(srRaySpatialNormQuadratic (E:=E)).PosDef:=by
    intro x hx
    have hn:(x:ℝ × E).2≠0:=by
      intro he
      apply hx
      apply (srRaySpatialEquiv (E:=E)).injective
      simpa only [map_zero] using he
    rw [sr_ray_spatial_norm_quadratic_value]
    exact sq_pos_of_pos (norm_pos_iff.mpr hn)
  apply sr_positive_quadratic_form_unique_from_full_unit_ball _ _
    (sr_source_spatial_positive (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) (srOccupiedIsotropicRaySource (E:=E))) hp
  intro x
  rw [← sr_source_spatial_recovers_full_clock_body (srRayClock (E:=E)) (srRayRestVector (E:=E))
    (sr_ray_rest_clock_one (E:=E)) (srOccupiedIsotropicRaySource (E:=E))]
  change x∈srCenteredClockBody (completedReach (srOriginalFutureRayIncrements (E:=E)))
    (srRayClock (E:=E)) (srRayRestVector (E:=E)) ↔ srRaySpatialNormQuadratic x≤1
  rw [sr_original_ray_clock_body_is_full_spatial_ball,Metric.mem_closedBall,dist_zero_right,
    sr_ray_spatial_kernel_norm,sr_ray_spatial_norm_quadratic_value]
  constructor <;> intro hh <;> nlinarith [norm_nonneg (x:ℝ × E).2]

theorem sr_full_ray_source_constructor_computes_lorentz_form_everywhere (z:ℝ × E) :
    srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E))
      (srOccupiedIsotropicRaySource (E:=E)) z=z.1^2-‖z.2‖^2 := by
  change srConstructedLorentzQuadratic (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E))
    (srSourceSpatialForm (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E)) (srOccupiedIsotropicRaySource (E:=E))) z=_
  rw [sr_constructed_lorentz_quadratic_value,
    sr_covariance_constructor_computes_the_original_ray_spatial_form,
    sr_ray_spatial_norm_quadratic_value]
  simp [srRayClock,srClockSpatialPart,srRayRestVector]

theorem sr_original_three_spatial_dimensions_give_four_dimensional_carrier :
    Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3))=4 := by simp

#print axioms sr_ray_spatial_norm_quadratic_value
#print axioms sr_covariance_constructor_computes_the_original_ray_spatial_form
#print axioms sr_full_ray_source_constructor_computes_lorentz_form_everywhere
#print axioms sr_original_three_spatial_dimensions_give_four_dimensional_carrier
end
end AASCMetricConstruction
