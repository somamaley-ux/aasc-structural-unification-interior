import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! SR 5.2: a homeomorphism normalizing the original displacement operations
is proved affine with an invertible real-linear displacement map. The proposed
frame is not received as an affine map or an isometry. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def srOriginalFrameDifference (F:V ≃ₜ V) (v:V) : V:=F v-F 0

theorem sr_normalized_original_translations_determine_all_displacement_answers
    (F:V ≃ₜ V) (normalizes:∀ v:V,∃ w:V,∀ x:V,F (x+v)=F x+w)
    (x v:V) : F (x+v)=F x+srOriginalFrameDifference F v := by
  obtain ⟨w,hw⟩:=normalizes v
  have he:=hw 0
  simp only [zero_add] at he
  have hd:srOriginalFrameDifference F v=w:=by rw [srOriginalFrameDifference,he];abel
  rw [hd]
  exact hw x

def srOriginalFrameDifferenceAddHom (F:V ≃ₜ V)
    (normalizes:∀ v:V,∃ w:V,∀ x:V,F (x+v)=F x+w) : V →+ V where
  toFun:=srOriginalFrameDifference F
  map_zero':=sub_self _
  map_add':=by
    intro u v
    rw [srOriginalFrameDifference,
      sr_normalized_original_translations_determine_all_displacement_answers F normalizes]
    change F u+srOriginalFrameDifference F v-F 0=
      (F u-F 0)+srOriginalFrameDifference F v
    abel

def srConstructedFrameLinearMap (F:V ≃ₜ V)
    (normalizes:∀ v:V,∃ w:V,∀ x:V,F (x+v)=F x+w) : V →L[ℝ] V:=
  (srOriginalFrameDifferenceAddHom F normalizes).toRealLinearMap
    (F.continuous.sub continuous_const)

theorem sr_constructed_frame_linear_map_bijective (F:V ≃ₜ V)
    (normalizes:∀ v:V,∃ w:V,∀ x:V,F (x+v)=F x+w) :
    Function.Bijective (srConstructedFrameLinearMap F normalizes) := by
  constructor
  · intro x y he
    apply F.injective
    change F x-F 0=F y-F 0 at he
    exact sub_left_injective he
  · intro v
    refine ⟨F.symm (v+F 0),?_⟩
    change F (F.symm (v+F 0))-F 0=v
    rw [F.apply_symm_apply,add_sub_cancel_right]

def srConstructedInvertibleFrameDisplacement (F:V ≃ₜ V)
    (normalizes:∀ v:V,∃ w:V,∀ x:V,F (x+v)=F x+w) : V ≃L[ℝ] V:=
  (LinearEquiv.ofBijective (srConstructedFrameLinearMap F normalizes).toLinearMap
    (sr_constructed_frame_linear_map_bijective F normalizes)).toContinuousLinearEquiv

theorem sr_original_frame_has_unique_constructed_affine_receipt (F:V ≃ₜ V)
    (normalizes:∀ v:V,∃ w:V,∀ x:V,F (x+v)=F x+w) :
    ∃! A:V ≃L[ℝ] V,∀ x:V,F x=A x+F 0 := by
  refine ⟨srConstructedInvertibleFrameDisplacement F normalizes,?_,?_⟩
  · intro x
    change F x=(F x-F 0)+F 0
    abel
  · intro A ha
    ext x
    have he:=ha x
    change A x=F x-F 0
    rw [he]
    abel

#print axioms sr_normalized_original_translations_determine_all_displacement_answers
#print axioms sr_constructed_frame_linear_map_bijective
#print axioms sr_original_frame_has_unique_constructed_affine_receipt
end
end AASCMetricConstruction
