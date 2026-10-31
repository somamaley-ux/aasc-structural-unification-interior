import SRRaySourceConstructedForm
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Genuine orientation-preserving spatial comparisons suffice for the native
ray source. Two actual hyperplane reflections produce determinant +1. This
removes reliance on allowing a single improper reflection in the rest family. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem sr_equal_length_vectors_related_by_orientation_preserving_isometry
    (dimension:2≤Module.finrank ℝ E) (x y:E) (norms:‖x‖=‖y‖) :
    ∃ A:E ≃ₗᵢ[ℝ] E,LinearMap.det A.toLinearMap=1 ∧ A x=y := by
  classical
  by_cases he:x=y
  · refine ⟨LinearIsometryEquiv.refl ℝ E,?_,he⟩
    change LinearMap.det (LinearMap.id: E →ₗ[ℝ] E)=1
    exact LinearMap.det_id
  have hy:y≠0:=by
    intro hz
    have hx:‖x‖=0:=by simpa [hz] using norms
    exact he ((norm_eq_zero.mp hx).trans hz.symm)
  let K:Submodule ℝ E:=(ℝ ∙ y)ᗮ
  have hk:0<Module.finrank ℝ K:=by
    have hh:1+Module.finrank ℝ K=Module.finrank ℝ E:=by
      simpa only [finrank_span_singleton hy] using
        (Submodule.finrank_add_finrank_orthogonal (ℝ ∙ y))
    omega
  have hn:¬Subsingleton K:=by
    intro hs
    have hh:Module.finrank ℝ K=0:=Module.finrank_zero_iff.mpr hs
    omega
  letI:Nontrivial K:=not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨z,hz⟩:=exists_ne (0:K)
  have hzne:(z:E)≠0:=by intro hh;exact hz (Subtype.ext hh)
  have hzy:inner ℝ (z:E) y=0:=Submodule.mem_orthogonal_singleton_iff_inner_left.mp z.property
  let R:E ≃ₗᵢ[ℝ] E:=Submodule.reflection (ℝ ∙ (x-y))ᗮ
  let S:E ≃ₗᵢ[ℝ] E:=Submodule.reflection (ℝ ∙ (z:E))ᗮ
  have hr:R x=y:=Submodule.reflection_sub norms
  have hs:S y=y:=Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hzy)
  have hdR:LinearMap.det R.toLinearMap=-1:=by
    change LinearMap.det ((ℝ ∙ (x-y))ᗮ.reflection.toLinearMap)=-1
    rw [Submodule.det_reflection,Submodule.orthogonal_orthogonal,
      finrank_span_singleton (sub_ne_zero.mpr he),pow_one]
  have hdS:LinearMap.det S.toLinearMap=-1:=by
    change LinearMap.det ((ℝ ∙ (z:E))ᗮ.reflection.toLinearMap)=-1
    rw [Submodule.det_reflection,Submodule.orthogonal_orthogonal,
      finrank_span_singleton hzne,pow_one]
  refine ⟨R.trans S,?_,?_⟩
  · change LinearMap.det (S.toLinearMap.comp R.toLinearMap)=1
    rw [LinearMap.det_comp,hdS,hdR]
    norm_num
  · change S (R x)=y
    rw [hr,hs]

abbrev SROrientedRayRest (E:Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  {A:E ≃ₗᵢ[ℝ] E | LinearMap.det A.toLinearMap=1}

def srOccupiedOrientedRaySource (dimension:2≤Module.finrank ℝ E) :
    SRStructuralConeSource (srRayClock (E:=E)) srRayRestVector (SROrientedRayRest E) where
  originalIncrements:=srOriginalFutureRayIncrements
  interiorRest:=sr_ray_rest_is_interior_of_original_completed_reach
  positiveCompletedClock:=sr_original_ray_completed_clock_strict
  rest:=fun A=>srRayRestComparison A.val
  preservesOriginal:=fun A=>sr_ray_rest_comparison_preserves_original_rays A.val
  clockPreserved:=fun A=>sr_ray_rest_comparison_clock A.val
  restFixed:=fun A=>sr_ray_rest_comparison_fixes_rest A.val
  boundaryIsotropy:=by
    intro x hx y hy
    rw [sr_original_ray_clock_body_is_full_spatial_ball,frontier_closedBall _ (by norm_num)] at hx hy
    have hnx:‖(x:ℝ × E).2‖=1:=by
      simpa only [Metric.mem_sphere,dist_zero_right,sr_ray_spatial_kernel_norm] using hx
    have hny:‖(y:ℝ × E).2‖=1:=by
      simpa only [Metric.mem_sphere,dist_zero_right,sr_ray_spatial_kernel_norm] using hy
    obtain ⟨A,hA,he⟩:=sr_equal_length_vectors_related_by_orientation_preserving_isometry
      dimension (x:ℝ × E).2 (y:ℝ × E).2 (hnx.trans hny.symm)
    refine ⟨⟨A,hA⟩,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.trans y.property.symm
    · exact he

theorem sr_three_dimensional_oriented_ray_source_is_jointly_occupied :
    Nonempty (SRStructuralConeSource
      (srRayClock (E:=EuclideanSpace ℝ (Fin 3))) srRayRestVector
      (SROrientedRayRest (EuclideanSpace ℝ (Fin 3)))) :=
  ⟨srOccupiedOrientedRaySource (by simp)⟩

#print axioms sr_equal_length_vectors_related_by_orientation_preserving_isometry
#print axioms srOccupiedOrientedRaySource
#print axioms sr_three_dimensional_oriented_ray_source_is_jointly_occupied
end
end AASCMetricConstruction
