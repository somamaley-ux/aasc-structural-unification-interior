import WickCovariantStrongSource
import KGNativeWickUnitRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wick_covariant_original_core_norm (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    ‖finiteParticleCoreToFock a (wickCovariantOriginalCore a f)‖ =
      ‖wickCovariantNaturalTest a f‖ := by
  rw [← wick_covariant_natural_original_core_square]
  rw [wick_isolated_covariant_norm]
  rfl

theorem wick_covariant_natural_norm_positive (a : Parameters)
    (f : 𝓢(Momentum,ℂ)) (hf : f ≠ 0) : 0 < ‖wickCovariantNaturalTest a f‖ := by
  apply norm_pos_iff.mpr
  intro hz
  exact hf ((wick_covariant_natural_test_injective a) (by simpa using hz))

theorem wick_covariant_original_core_nonzero (a : Parameters)
    (f : 𝓢(Momentum,ℂ)) (hf : f ≠ 0) : wickCovariantOriginalCore a f ≠ 0 := by
  intro hz
  have h := wick_covariant_natural_norm_positive a f hf
  rw [← wick_covariant_original_core_norm, hz, map_zero, norm_zero] at h
  exact (lt_irrefl 0) h

def wickCovariantUnitTest (a : Parameters) (f : 𝓢(Momentum,ℂ)) : 𝓢(Momentum,ℂ) :=
  ((‖wickCovariantNaturalTest a f‖⁻¹ : ℝ) : ℂ) • f

theorem wick_covariant_unit_test_norm (a : Parameters)
    (f : 𝓢(Momentum,ℂ)) (hf : f ≠ 0) :
    ‖wickCovariantNaturalTest a (wickCovariantUnitTest a f)‖ = 1 := by
  have hn := wick_covariant_natural_norm_positive a f hf
  have hc : ‖((‖wickCovariantNaturalTest a f‖⁻¹ : ℝ) : ℂ)‖ =
      ‖wickCovariantNaturalTest a f‖⁻¹ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
  rw [wickCovariantUnitTest, map_smul, norm_smul, hc, inv_mul_cancel₀ hn.ne']

theorem wick_covariant_unit_test_original_square (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    wickCovariantOriginalCore a (wickCovariantUnitTest a f) =
      originalWickUnitRepresentative a (wickCovariantOriginalCore a f) := by
  rw [wickCovariantUnitTest, map_smul, originalWickUnitRepresentative,
    wick_covariant_original_core_norm]

end AASCKleinGordon
