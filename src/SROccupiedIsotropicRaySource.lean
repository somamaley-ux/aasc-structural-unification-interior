import SROccupiedRayReach
import SRSourceConeLineage
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A nonvacuous calibrated geometric source branch of SR 15.7. Original
positive-duration rays, their exact finite/completed reach, the strict clock,
interior rest record, and full boundary isotropy are all derived. The model's
rest family here includes all spatial linear isometries; an independently fixed
orientation-preserving-only protocol family requires its own subgroup receipt.
This is not a claim that all SR 15.3--15.6 body/scattering/device laws are encoded. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
open scoped Topology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def srRayClock : (ℝ × E) →L[ℝ] ℝ:=ContinuousLinearMap.fst ℝ ℝ E
def srRayRestVector : ℝ × E:=(1,0)

theorem sr_ray_rest_clock_one : srRayClock (srRayRestVector (E:=E))=1 := rfl

def srRaySpatialEquiv : SRClockSpatialSpace (srRayClock (E:=E)) ≃L[ℝ] E:=
  (show SRClockSpatialSpace (srRayClock (E:=E)) ≃ₗ[ℝ] E from
    { toFun:=fun x=>(x:ℝ × E).2
      invFun:=fun y=>⟨(0,y),rfl⟩
      map_add':=fun _ _=>rfl
      map_smul':=fun _ _=>rfl
      left_inv:=by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · exact x.property.symm
        · rfl
      right_inv:=fun _=>rfl }).toContinuousLinearEquiv

instance sr_ray_spatial_nontrivial : Nontrivial (SRClockSpatialSpace (srRayClock (E:=E))) := by
  obtain ⟨x,y,hxy⟩:=exists_pair_ne E
  refine ⟨⟨srRaySpatialEquiv.symm x,srRaySpatialEquiv.symm y,?_⟩⟩
  intro he
  apply hxy
  have hh:=congrArg (srRaySpatialEquiv (E:=E)) he
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh

theorem sr_ray_spatial_kernel_norm (x : SRClockSpatialSpace (srRayClock (E:=E))) :
    ‖x‖=‖(x:ℝ × E).2‖ := by
  have hx:(x:ℝ × E).1=0:=x.property
  change max ‖(x:ℝ × E).1‖ ‖(x:ℝ × E).2‖=‖(x:ℝ × E).2‖
  rw [hx,norm_zero,max_eq_right (norm_nonneg _)]

theorem sr_ray_rest_is_interior_of_original_completed_reach :
    srRayRestVector (E:=E)∈interior (completedReach srOriginalFutureRayIncrements) := by
  rw [sr_original_ray_completed_reach_exact_full_cone]
  let U:Set (ℝ × E):={z|‖z.2‖<z.1}
  have hu:IsOpen U:=isOpen_lt continuous_snd.norm continuous_fst
  have he:srRayRestVector (E:=E)∈U:=by norm_num [U,srRayRestVector]
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hu.mem_nhds he)
  intro z hz
  change ‖z.2‖<z.1 at hz
  exact hz.le

def srRayRestComparison (A:E ≃ₗᵢ[ℝ] E) : (ℝ × E) ≃L[ℝ] (ℝ × E):=
  (LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) A.toLinearEquiv).toContinuousLinearEquiv

theorem sr_ray_rest_comparison_value (A:E ≃ₗᵢ[ℝ] E) (z:ℝ × E) :
    srRayRestComparison A z=(z.1,A z.2) := rfl

theorem sr_ray_rest_comparison_clock (A:E ≃ₗᵢ[ℝ] E) (z:ℝ × E) :
    srRayClock (srRayRestComparison A z)=srRayClock z := rfl

theorem sr_ray_rest_comparison_fixes_rest (A:E ≃ₗᵢ[ℝ] E) :
    srRayRestComparison A srRayRestVector=srRayRestVector := by
  rw [sr_ray_rest_comparison_value]
  simp [srRayRestVector]

theorem sr_ray_rest_comparison_preserves_original_rays (A:E ≃ₗᵢ[ℝ] E) :
    srRayRestComparison A '' srOriginalFutureRayIncrements=srOriginalFutureRayIncrements := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa only [sr_ray_rest_comparison_value,srOriginalFutureRayIncrements,mem_setOf_eq,
      LinearIsometryEquiv.norm_map] using hw
  · intro hz
    refine ⟨(z.1,A.symm z.2),?_,?_⟩
    · simpa only [srOriginalFutureRayIncrements,mem_setOf_eq,LinearIsometryEquiv.norm_map] using hz
    · rw [sr_ray_rest_comparison_value]
      simp only [A.apply_symm_apply,Prod.mk.eta]

theorem sr_original_ray_clock_body_is_full_spatial_ball :
    srCenteredClockBody (completedReach srOriginalFutureRayIncrements)
      (srRayClock (E:=E)) srRayRestVector=Metric.closedBall 0 1 := by
  rw [sr_original_ray_completed_reach_exact_full_cone]
  ext x
  have hx:(x:ℝ × E).1=0:=x.property
  change ‖(0:E)+(x:ℝ × E).2‖≤1+(x:ℝ × E).1 ↔ dist x 0≤1
  rw [zero_add,hx,add_zero,dist_zero_right,sr_ray_spatial_kernel_norm]

theorem sr_original_ray_full_boundary_isotropy :
    ∀ x∈frontier (srCenteredClockBody (completedReach srOriginalFutureRayIncrements)
      (srRayClock (E:=E)) srRayRestVector),
    ∀ y∈frontier (srCenteredClockBody (completedReach srOriginalFutureRayIncrements)
      (srRayClock (E:=E)) srRayRestVector),
    ∃ A:E ≃ₗᵢ[ℝ] E,
      srRestOnClockKernel srRayClock (srRayRestComparison A) (sr_ray_rest_comparison_clock A) x=y := by
  intro x hx y hy
  rw [sr_original_ray_clock_body_is_full_spatial_ball,frontier_closedBall _ (by norm_num)] at hx hy
  have hnx:‖(x:ℝ × E).2‖=1:=by
    simpa only [Metric.mem_sphere,dist_zero_right,sr_ray_spatial_kernel_norm] using hx
  have hny:‖(y:ℝ × E).2‖=1:=by
    simpa only [Metric.mem_sphere,dist_zero_right,sr_ray_spatial_kernel_norm] using hy
  let A:E ≃ₗᵢ[ℝ] E:=Submodule.reflection (ℝ ∙ ((x:ℝ × E).2-(y:ℝ × E).2))ᗮ
  have he:A (x:ℝ × E).2=(y:ℝ × E).2:=Submodule.reflection_sub (hnx.trans hny.symm)
  refine ⟨A,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (x:ℝ × E).1=(y:ℝ × E).1
    exact x.property.trans y.property.symm
  · exact he

def srOccupiedIsotropicRaySource : SRStructuralConeSource (srRayClock (E:=E)) srRayRestVector
    (E ≃ₗᵢ[ℝ] E) where
  originalIncrements:=srOriginalFutureRayIncrements
  interiorRest:=sr_ray_rest_is_interior_of_original_completed_reach
  positiveCompletedClock:=sr_original_ray_completed_clock_strict
  rest:=srRayRestComparison
  preservesOriginal:=sr_ray_rest_comparison_preserves_original_rays
  clockPreserved:=sr_ray_rest_comparison_clock
  restFixed:=sr_ray_rest_comparison_fixes_rest
  boundaryIsotropy:=sr_original_ray_full_boundary_isotropy

theorem sr_four_dimensional_ray_source_conditions_are_jointly_inhabited :
    Nonempty (SRStructuralConeSource
      (srRayClock (E:=EuclideanSpace ℝ (Fin 3))) srRayRestVector
      (EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))) :=
  ⟨srOccupiedIsotropicRaySource⟩

#print axioms sr_ray_rest_clock_one
#print axioms srRaySpatialEquiv
#print axioms sr_ray_spatial_nontrivial
#print axioms sr_ray_spatial_kernel_norm
#print axioms sr_ray_rest_is_interior_of_original_completed_reach
#print axioms sr_ray_rest_comparison_value
#print axioms sr_ray_rest_comparison_clock
#print axioms sr_ray_rest_comparison_fixes_rest
#print axioms sr_ray_rest_comparison_preserves_original_rays
#print axioms sr_original_ray_clock_body_is_full_spatial_ball
#print axioms sr_original_ray_full_boundary_isotropy
#print axioms srOccupiedIsotropicRaySource
#print axioms sr_four_dimensional_ray_source_conditions_are_jointly_inhabited
end
end AASCMetricConstruction
