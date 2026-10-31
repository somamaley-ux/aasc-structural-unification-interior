import WickSpatialTransferDensity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem wick_transfer_phase_integrable (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ))
    (x : WickSpaceSlice) :
    Integrable (fun z : WickSpaceSlice × WickSpaceSlice =>
      Real.fourierChar (-inner ℝ z.2 x) • wickTransferKernelCLM H z)
      ((volume : Measure WickSpaceSlice).prod (volume : Measure WickSpaceSlice)) := by
  letI : Measure.IsAddHaarMeasure
      ((volume : Measure WickSpaceSlice).prod (volume : Measure WickSpaceSlice)) := inferInstance
  have base : Integrable (wickTransferKernelCLM H)
      ((volume : Measure WickSpaceSlice).prod (volume : Measure WickSpaceSlice)) :=
    (wickTransferKernelCLM H).integrable
  apply base.norm.mono'
    (((Real.continuous_fourierChar.comp ((continuous_snd.inner continuous_const).neg)).smul
      (wickTransferKernelCLM H).continuous).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun z => (Circle.norm_smul _ _).le)

theorem wick_transfer_fourier_is_actual_kernel_integral
    (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) (x : WickSpaceSlice) :
    (𝓕 (wickSpatialTransferDensityCLM H) : 𝓢(WickSpaceSlice,ℂ)) x =
      ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
        Real.fourierChar (-inner ℝ (p-q) x) • H (p,q) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  simp_rw [wick_spatial_transfer_density_apply]
  calc
    _=∫ k : WickSpaceSlice,∫ p : WickSpaceSlice,
        Real.fourierChar (-inner ℝ k x) • wickTransferKernelCLM H (p,k) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun k => by
        dsimp only
        change (Real.fourierChar (-inner ℝ k x) : ℂ)*(∫ p,H (p,p-k)) =
          ∫ p : WickSpaceSlice,(Real.fourierChar (-inner ℝ k x) : ℂ)*H (p,p-k)
        exact (integral_const_mul _ _).symm)
    _=∫ p : WickSpaceSlice,∫ k : WickSpaceSlice,
        Real.fourierChar (-inner ℝ k x) • wickTransferKernelCLM H (p,k) :=
      (integral_integral_swap (wick_transfer_phase_integrable H x)).symm
    _=_ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by
        have substitute := integral_sub_left_eq_self
          (fun q : WickSpaceSlice => Real.fourierChar (-inner ℝ (p-q) x) • H (p,q)) volume p
        simpa only [sub_sub_cancel] using substitute)

theorem wick_actual_spatial_kernel_integral_is_diagonal
    (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) :
    (∫ x : WickSpaceSlice,∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
      Real.fourierChar (-inner ℝ (p-q) x) • H (p,q)) = ∫ p,H (p,p) := by
  simp_rw [← wick_transfer_fourier_is_actual_kernel_integral]
  exact wick_spatial_transfer_integral_fourier_diagonal H

theorem wick_actual_spatial_kernel_integrable (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) :
    Integrable (fun x : WickSpaceSlice => ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
      Real.fourierChar (-inner ℝ (p-q) x) • H (p,q)) := by
  simpa only [← wick_transfer_fourier_is_actual_kernel_integral] using
    wick_spatial_transfer_density_fourier_integrable H

end AASCKleinGordon
