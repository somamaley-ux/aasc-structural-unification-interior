import SRNativeFlatSmoothComparisons
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Bundle the proved smooth native translation orbit into Mathlib's actual
manifold diffeomorphism. This concerns the original explicit flat model;
general Lie-quotient/exponential construction is not assumed or claimed. -/
namespace AASCMetricConstruction
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def srNativeOriginalTranslationOrbitDiffeomorph (o : V) :
    Diffeomorph 𝓘(ℝ,V) 𝓘(ℝ,V) V V ∞ where
  toEquiv := (srNativeTranslationOrbitChart o).toEquiv
  contMDiff_toFun := (sr_native_original_translation_orbit_is_smooth_diffeomorphism o).1.contMDiff
  contMDiff_invFun := (sr_native_original_translation_orbit_is_smooth_diffeomorphism o).2.contMDiff

theorem sr_native_bundled_orbit_retains_actual_original_translation (o v : V) :
    srNativeOriginalTranslationOrbitDiffeomorph o v = o+v ∧
      (srNativeOriginalTranslationOrbitDiffeomorph o).symm v = v-o := ⟨rfl,rfl⟩

theorem sr_native_comparison_one_parameter_is_smooth (v : V) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ,V) ∞ (srNativeTranslationOneParameter v) :=
  (show ContDiff ℝ ∞ (srNativeTranslationOneParameter v) from contDiff_id.smul contDiff_const).contMDiff

#print axioms srNativeOriginalTranslationOrbitDiffeomorph
#print axioms sr_native_bundled_orbit_retains_actual_original_translation
#print axioms sr_native_comparison_one_parameter_is_smooth
end
end AASCMetricConstruction
