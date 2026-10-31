import SROrientationPreservingRayIsotropy
import SRCompletedOrderMetricConstruction

/-! The native oriented ray branch jointly instantiates completed antisymmetry,
weak duration, the actual proper-rotation group, no fixed spatial vector and
whole-boundary isotropy. General clock separation now applies to that same W. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Set
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

def srOrientationPreservingRestSubgroup : Subgroup (E ≃ₗᵢ[ℝ] E) where
  carrier:={A|LinearMap.det A.toLinearMap=1}
  one_mem':=by
    change LinearMap.det (LinearMap.id:E →ₗ[ℝ] E)=1
    exact LinearMap.det_id
  mul_mem':=by
    intro A B hA hB
    change LinearMap.det (A.toLinearMap.comp B.toLinearMap)=1
    rw [LinearMap.det_comp,hA,hB,mul_one]
  inv_mem':=by
    intro A hA
    have he:A.symm.toLinearMap.comp A.toLinearMap=(LinearMap.id:E →ₗ[ℝ] E):=by
      ext x
      exact A.symm_apply_apply x
    have hd:=congrArg LinearMap.det he
    rw [LinearMap.det_comp,hA,mul_one,LinearMap.det_id] at hd
    exact hd

instance sr_oriented_ray_rest_group : Group (SROrientedRayRest E):=
  inferInstanceAs (Group ↥(srOrientationPreservingRestSubgroup (E:=E)))

def srOrientedRaySpacetimeRest : SROrientedRayRest E →* ((ℝ × E) ≃L[ℝ] (ℝ × E)) where
  toFun A:=srRayRestComparison A.val
  map_one':=by ext z <;> rfl
  map_mul' A B:=by ext z <;> rfl

theorem sr_native_original_ray_completed_order_is_antisymmetric
    (v:ℝ × E) (forward:v∈completedReach srOriginalFutureRayIncrements)
    (backward:-v∈completedReach srOriginalFutureRayIncrements) : v=0 := by
  rw [sr_original_ray_completed_reach_exact_full_cone] at forward backward
  change ‖v.2‖≤v.1 at forward
  change ‖-v.2‖≤-v.1 at backward
  rw [norm_neg] at backward
  have hx:‖v.2‖=0:=by nlinarith [norm_nonneg v.2]
  have ht:v.1=0:=by linarith
  exact Prod.ext ht (norm_eq_zero.mp hx)

theorem sr_native_proper_rotations_have_no_fixed_spatial_vector
    (dimension:2≤Module.finrank ℝ E) (v:ℝ × E)
    (spatial:(srRayClock (E:=E)) v=0)
    (fixed:∀ A:SROrientedRayRest E,srOrientedRaySpacetimeRest A v=v) : v=0 := by
  obtain ⟨A,hA,he⟩:=sr_equal_length_vectors_related_by_orientation_preserving_isometry
    dimension v.2 (-v.2) (norm_neg _).symm
  have hf:=congrArg Prod.snd (fixed ⟨A,hA⟩)
  change A v.2=v.2 at hf
  have hh:v.2+v.2=0:=by
    calc
      v.2+v.2=(-v.2)+v.2:=congrArg (fun w:E=>w+v.2) (hf.symm.trans he)
      _=0:=neg_add_cancel _
  have h2:(2:ℝ) • v.2=0:=by simpa only [two_smul] using hh
  have hx:v.2=0:=(smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact Prod.ext spatial hx

def srNativeOrientedCompletedOrderSource (dimension:2≤Module.finrank ℝ E) :
    SRCompletedOrderSource (H:=SROrientedRayRest E)
      (srRayClock (E:=E)) (srRayRestVector (E:=E)) where
  originalIncrements:=srOriginalFutureRayIncrements
  originalClockNonnegative:=fun _ hw=>hw.1.le
  completedAntisymmetry:=sr_native_original_ray_completed_order_is_antisymmetric
  interiorRest:=sr_ray_rest_is_interior_of_original_completed_reach
  rest:=srOrientedRaySpacetimeRest
  preservesOriginal:=fun A=>sr_ray_rest_comparison_preserves_original_rays A.val
  clockPreserved:=fun A=>sr_ray_rest_comparison_clock A.val
  restFixed:=fun A=>sr_ray_rest_comparison_fixes_rest A.val
  noFixedSpatial:=sr_native_proper_rotations_have_no_fixed_spatial_vector dimension
  boundaryIsotropy:=(srOccupiedOrientedRaySource dimension).boundaryIsotropy

theorem sr_native_oriented_completed_order_derives_strict_clock_and_lorentz_form
    (dimension:2≤Module.finrank ℝ E) :
    (∀ v∈completedReach (srOriginalFutureRayIncrements (E:=E)),v≠0 → 0<(srRayClock (E:=E)) v) ∧
    (srSourceLorentzForm (srRayClock (E:=E)) (srRayRestVector (E:=E)) (sr_ray_rest_clock_one (E:=E))
      (srCompletedOrderToConeSource (srRayClock (E:=E)) (srRayRestVector (E:=E))
        (srNativeOrientedCompletedOrderSource (E:=E) dimension))).associated.SeparatingLeft := by
  exact ⟨sr_original_completed_order_source_derives_strict_clock (srRayClock (E:=E)) (srRayRestVector (E:=E))
    (srNativeOrientedCompletedOrderSource (E:=E) dimension),
    sr_completed_order_constructed_lorentz_form_nondegenerate (srRayClock (E:=E)) (srRayRestVector (E:=E))
      (sr_ray_rest_clock_one (E:=E)) (srNativeOrientedCompletedOrderSource (E:=E) dimension)⟩

#print axioms srOrientationPreservingRestSubgroup
#print axioms sr_oriented_ray_rest_group
#print axioms srOrientedRaySpacetimeRest
#print axioms sr_native_original_ray_completed_order_is_antisymmetric
#print axioms sr_native_proper_rotations_have_no_fixed_spatial_vector
#print axioms srNativeOrientedCompletedOrderSource
#print axioms sr_native_oriented_completed_order_derives_strict_clock_and_lorentz_form
end
end AASCMetricConstruction
