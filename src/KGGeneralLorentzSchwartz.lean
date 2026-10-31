import KGGeneralLorentzMassShell
import KGLorentzBoostSchwartz

noncomputable section
set_option maxHeartbeats 1600000
open scoped SchwartzMap
namespace AASCKleinGordon

def properLorentzFourCLE (L : ProperLorentzTransform) : FourMomentum ≃L[ℝ] FourMomentum :=
  L.val.toContinuousLinearEquiv

theorem lorentzShellMap_eq_projection (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    lorentzShellMap a L p=fourSpatialProjection (properLorentzFourCLE L (massShell a p)) := by
  funext j
  fin_cases j <;> rfl

theorem lorentzShellMap_temperate (a : Parameters) (L : ProperLorentzTransform) :
    (lorentzShellMap a L).HasTemperateGrowth := by
  have h:=fourSpatialProjection.hasTemperateGrowth.comp
    ((properLorentzFourCLE L).toContinuousLinearMap.hasTemperateGrowth.comp (massShell_temperate a))
  convert h using 1

theorem lorentzShellMap_polynomial_inverse_bound (a : Parameters) (L : ProperLorentzTransform) :
    ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖≤C*(1+‖lorentzShellMap a L p‖)^k := by
  obtain ⟨k,C,h⟩:=(lorentzShellMap_temperate a L⁻¹).2 0
  refine ⟨k,C,fun p => ?_⟩
  simpa only [norm_iteratedFDeriv_zero,lorentzShellMap_inverse_left] using h (lorentzShellMap a L p)

def lorentzSchwartzCLM (a : Parameters) (L : ProperLorentzTransform) :
    𝓢(Momentum,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  SchwartzMap.compCLM ℂ (lorentzShellMap_temperate a L⁻¹)
    (lorentzShellMap_polynomial_inverse_bound a L⁻¹)

@[simp] theorem lorentzSchwartzCLM_apply (a : Parameters) (L : ProperLorentzTransform)
    (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    lorentzSchwartzCLM a L f p=f (lorentzShellMap a L⁻¹ p) := rfl

theorem lorentzSchwartz_one (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    lorentzSchwartzCLM a 1 f=f := by
  ext p
  simp only [lorentzSchwartzCLM_apply,inv_one,lorentzShellMap_one]

theorem lorentzSchwartz_mul (a : Parameters) (L M : ProperLorentzTransform) (f : 𝓢(Momentum,ℂ)) :
    lorentzSchwartzCLM a L (lorentzSchwartzCLM a M f)=lorentzSchwartzCLM a (L*M) f := by
  ext p
  simp only [lorentzSchwartzCLM_apply,mul_inv_rev,lorentzShellMap_mul]

theorem lorentzSchwartz_inverse (a : Parameters) (L : ProperLorentzTransform) (f : 𝓢(Momentum,ℂ)) :
    lorentzSchwartzCLM a L⁻¹ (lorentzSchwartzCLM a L f)=f := by
  rw [lorentzSchwartz_mul,inv_mul_cancel,lorentzSchwartz_one]

def lorentzSchwartzCLE (a : Parameters) (L : ProperLorentzTransform) :
    𝓢(Momentum,ℂ) ≃L[ℂ] 𝓢(Momentum,ℂ) where
  toLinearEquiv:=
    { toLinearMap:=(lorentzSchwartzCLM a L).toLinearMap
      invFun:=lorentzSchwartzCLM a L⁻¹
      left_inv:=lorentzSchwartz_inverse a L
      right_inv:=by intro f; simpa only [inv_inv] using lorentzSchwartz_inverse a L⁻¹ f }
  continuous_toFun:=(lorentzSchwartzCLM a L).continuous
  continuous_invFun:=(lorentzSchwartzCLM a L⁻¹).continuous

end AASCKleinGordon
