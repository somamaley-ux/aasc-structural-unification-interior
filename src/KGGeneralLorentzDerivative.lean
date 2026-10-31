import KGGeneralLorentzSchwartz
import KGLorentzBoostJacobian

noncomputable section
namespace AASCKleinGordon

def massShellDerivativeCLM (a : Parameters) (p : Momentum) : Momentum →L[ℝ] FourMomentum :=
  fourTimeInjection.comp (a.speed⁻¹ • energyDerivativeCLM a p)+fourSpatialInjection

theorem massShell_hasFDerivAt (a : Parameters) (p : Momentum) :
    HasFDerivAt (massShell a) (massShellDerivativeCLM a p) p := by
  have he : HasFDerivAt (fun q : Momentum => energy a q/a.speed)
      (a.speed⁻¹ • energyDerivativeCLM a p) p := by
    simpa only [div_eq_mul_inv,mul_comm] using (energy_hasFDerivAt a p).const_mul a.speed⁻¹
  have hs:=(fourTimeInjection.hasFDerivAt.comp p he).add fourSpatialInjection.hasFDerivAt
  convert hs using 1
  funext q
  exact massShell_eq_injections a q

def lorentzShellDerivativeCLM (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    Momentum →L[ℝ] Momentum :=
  fourSpatialProjection.comp ((properLorentzFourCLE L).toContinuousLinearMap.comp
    (massShellDerivativeCLM a p))

theorem lorentzShellMap_hasFDerivAt (a : Parameters) (L : ProperLorentzTransform) (p : Momentum) :
    HasFDerivAt (lorentzShellMap a L) (lorentzShellDerivativeCLM a L p) p := by
  have h:=fourSpatialProjection.hasFDerivAt.comp p
    ((properLorentzFourCLE L).hasFDerivAt.comp p (massShell_hasFDerivAt a p))
  convert h using 1

theorem lorentzShell_derivative_intertwines (a : Parameters) (L : ProperLorentzTransform)
    (p : Momentum) :
    (properLorentzFourCLE L).toContinuousLinearMap.comp (massShellDerivativeCLM a p)=
      (massShellDerivativeCLM a (lorentzShellMap a L p)).comp (lorentzShellDerivativeCLM a L p) := by
  have hl:=(properLorentzFourCLE L).hasFDerivAt.comp p (massShell_hasFDerivAt a p)
  have hr:=(massShell_hasFDerivAt a (lorentzShellMap a L p)).comp p
    (lorentzShellMap_hasFDerivAt a L p)
  have he : (fun q => properLorentzFourCLE L (massShell a q))=
      (fun q => massShell a (lorentzShellMap a L q)) := by
    funext q
    exact (massShell_lorentzShellMap a L q).symm
  change HasFDerivAt (fun q => properLorentzFourCLE L (massShell a q)) _ p at hl
  rw [he] at hl
  exact hl.unique hr

end AASCKleinGordon
