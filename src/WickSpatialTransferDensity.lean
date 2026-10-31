import WickSchwartzPartialIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

abbrev WickSpaceSlice := EuclideanSpace ℝ (Fin 3)

def wickTransferShear : (WickSpaceSlice × WickSpaceSlice) ≃L[ℝ]
    (WickSpaceSlice × WickSpaceSlice) where
  toLinearEquiv :=
    { toFun z := (z.1,z.1-z.2)
      invFun z := (z.1,z.1-z.2)
      map_add' z w := by ext <;> simp <;> abel
      map_smul' c z := by ext <;> simp [smul_sub]
      left_inv z := by ext <;> simp
      right_inv z := by ext <;> simp }
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)

def wickTransferKernelCLM : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ) →L[ℂ]
    𝓢(WickSpaceSlice × WickSpaceSlice,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ wickTransferShear

def wickSpatialTransferDensityCLM : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ) →L[ℂ]
    𝓢(WickSpaceSlice,ℂ) :=
  (wickSchwartzPartialIntegralCLM (volume : Measure WickSpaceSlice)).comp wickTransferKernelCLM

theorem wick_spatial_transfer_density_apply (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ))
    (k : WickSpaceSlice) : wickSpatialTransferDensityCLM H k=∫ p,H (p,p-k) := by
  rw [wickSpatialTransferDensityCLM, ContinuousLinearMap.comp_apply,
    wick_schwartz_partial_integral_apply]
  rfl

theorem wick_spatial_transfer_density_diagonal (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) :
    wickSpatialTransferDensityCLM H 0=∫ p,H (p,p) := by
  rw [wick_spatial_transfer_density_apply]
  simp only [sub_zero]

theorem wick_spatial_transfer_density_fourier_integrable
    (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) :
    Integrable (fun x : WickSpaceSlice =>
      (𝓕 (wickSpatialTransferDensityCLM H) : 𝓢(WickSpaceSlice,ℂ)) x) :=
  (𝓕 (wickSpatialTransferDensityCLM H) : 𝓢(WickSpaceSlice,ℂ)).integrable

theorem wick_spatial_transfer_integral_fourier_diagonal
    (H : 𝓢(WickSpaceSlice × WickSpaceSlice,ℂ)) :
    (∫ x : WickSpaceSlice,(𝓕 (wickSpatialTransferDensityCLM H) : 𝓢(WickSpaceSlice,ℂ)) x)=∫ p,H (p,p) := by
  have inversion := congrArg (fun f : 𝓢(WickSpaceSlice,ℂ) => f 0)
    (FourierTransform.fourierInv_fourier_eq (F:=𝓢(WickSpaceSlice,ℂ)) (wickSpatialTransferDensityCLM H))
  dsimp only at inversion
  rw [wick_spatial_transfer_density_diagonal] at inversion
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, inner_zero_left, inner_zero_right,
    neg_zero, AddChar.map_zero_eq_one, one_smul] using inversion

end AASCKleinGordon
