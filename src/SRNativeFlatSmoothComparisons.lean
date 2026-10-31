import SRNativeWholeSourceComparisons
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Smooth bridge for the explicitly selected native flat translation model.
The arbitrary abelian Lie-group exponential/closed-quotient theorem of SR 5.3
is a different remaining task. No arbitrary Lie isomorphism is assumed here.
The native original event action is p ↦ p+d, on its already selected real
comparison carrier. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open scoped ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def srNativeTranslationOneParameter (v : V) : ℝ →+ V where
  toFun := fun t => t • v
  map_zero' := zero_smul ℝ v
  map_add' := fun s t => add_smul s t v

theorem sr_native_translation_one_parameter_actual_tangent (v : V) (t : ℝ) :
    HasDerivAt (srNativeTranslationOneParameter v) v t := by
  simpa only [one_smul] using (hasDerivAt_id t).smul_const v

theorem sr_native_translation_constant_tangent_solution_unique (v : V) (c : ℝ → V)
    (initial : c 0 = 0) (equation : ∀ t, HasDerivAt c v t) :
    c = srNativeTranslationOneParameter v := by
  have hd (t : ℝ) : HasDerivAt (fun s => c s - srNativeTranslationOneParameter v s) 0 t := by
    simpa only [sub_self] using (equation t).sub
      (sr_native_translation_one_parameter_actual_tangent v t)
  funext t
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa [srNativeTranslationOneParameter, initial, sub_eq_zero] using he

def srNativeTranslationExponential (v : V) : V := srNativeTranslationOneParameter v 1

theorem sr_native_translation_exponential_is_identity :
    srNativeTranslationExponential (V := V) = id := by
  funext v
  exact one_smul ℝ v

theorem sr_native_translation_exponential_smooth_and_linear :
    ContDiff ℝ ∞ (srNativeTranslationExponential (V := V)) ∧
      (∀ u v : V, srNativeTranslationExponential (u+v) =
        srNativeTranslationExponential u + srNativeTranslationExponential v) := by
  rw [sr_native_translation_exponential_is_identity]
  exact ⟨contDiff_id,fun _ _ => rfl⟩

def srNativeTranslationOrbitChart (o : V) : V ≃ₜ V where
  toFun := fun v => o+v
  invFun := fun x => x-o
  left_inv := fun v => by simp [add_comm, add_left_comm, add_assoc]
  right_inv := fun x => by simp [add_comm, add_left_comm, add_assoc]
  continuous_toFun := continuous_const.add continuous_id
  continuous_invFun := continuous_id.sub continuous_const

theorem sr_native_original_translation_orbit_is_smooth_diffeomorphism (o : V) :
    ContDiff ℝ ∞ (srNativeTranslationOrbitChart o) ∧
      ContDiff ℝ ∞ (srNativeTranslationOrbitChart o).symm :=
  ⟨contDiff_const.add contDiff_id, contDiff_id.sub contDiff_const⟩

theorem sr_native_original_translation_orbit_tangent_is_identity (o v : V) :
    HasFDerivAt (srNativeTranslationOrbitChart o) (ContinuousLinearMap.id ℝ V) v :=
  (hasFDerivAt_id v).const_add o

#print axioms sr_native_translation_one_parameter_actual_tangent
#print axioms sr_native_translation_constant_tangent_solution_unique
#print axioms sr_native_translation_exponential_is_identity
#print axioms sr_native_translation_exponential_smooth_and_linear
#print axioms sr_native_original_translation_orbit_is_smooth_diffeomorphism
#print axioms sr_native_original_translation_orbit_tangent_is_identity
end
end AASCMetricConstruction
