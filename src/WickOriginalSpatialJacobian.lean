import WickSpatialFourierDiagonal
import WickChargeMeasureCoefficient
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

/-- The actual original shell-frequency scale, with its derived three-space
Jacobian. This does not assume that the physical Wigner-weighted transfer
kernel has already been identified with an arbitrary H. -/
theorem wick_original_scaled_spatial_integral (a : Parameters)
    (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) :
    (∫ x : WickSpaceSlice,∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
      Real.fourierChar (-inner ℝ ((fourierWaveScale a) • (p-q)) x) • H (p,q)) =
      (wickSpatialFourierJacobian a : ℂ)*(∫ p,H (p,p)) := by
  have scaled := Measure.integral_comp_smul_of_nonneg (volume : Measure WickSpaceSlice)
    (fun x : WickSpaceSlice => ∫ p : WickSpaceSlice,∫ q : WickSpaceSlice,
      Real.fourierChar (-inner ℝ (p-q) x) • H (p,q))
    (fourierWaveScale a) (hR:=(fourierWaveScale_pos a).le)
  rw [wick_actual_spatial_kernel_integral_is_diagonal] at scaled
  simpa only [WickSpaceSlice, finrank_euclideanSpace, Fintype.card_fin, inv_pow,
    wickSpatialFourierJacobian, inner_smul_left, inner_smul_right, conj_trivial,
    RCLike.real_smul_eq_coe_mul] using scaled

end AASCKleinGordon
