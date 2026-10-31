import KGGeneralLorentzMeasure
import KGOneParticleBoostUnitary

noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

def lorentzMomentumME (a : Parameters) (L : ProperLorentzTransform) : Momentum ≃ᵐ Momentum where
  toEquiv:=lorentzShellEquiv a L
  measurable_toFun:=(lorentzShellMap_temperate a L).1.continuous.measurable
  measurable_invFun:=(lorentzShellMap_temperate a L⁻¹).1.continuous.measurable

def oneParticleLorentzUnitary (a : Parameters) (L : ProperLorentzTransform) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] OneParticleHilbert a :=
  lpMeasureEquivalence (lorentzMomentumME a L⁻¹)
    (lorentzShellMap_preserves_wignerMeasure a L⁻¹)
    (MeasurePreserving.symm (lorentzMomentumME a L⁻¹)
      (lorentzShellMap_preserves_wignerMeasure a L⁻¹))

theorem oneParticleLorentzUnitary_ae (a : Parameters) (L : ProperLorentzTransform)
    (f : OneParticleHilbert a) :
    (oneParticleLorentzUnitary a L f : Momentum → ℂ)=ᵐ[wignerMeasure a]
      (fun p => f (lorentzShellMap a L⁻¹ p)) :=
  Lp.coeFn_compMeasurePreserving f (lorentzShellMap_preserves_wignerMeasure a L⁻¹)

theorem oneParticleLorentzUnitary_intertwines_original_schwartz (a : Parameters)
    (L : ProperLorentzTransform) (f : 𝓢(Momentum,ℂ)) :
    oneParticleLorentzUnitary a L (oneParticleSchwartzToHilbert a f)=
      oneParticleSchwartzToHilbert a (lorentzSchwartzCLM a L f) := by
  apply Lp.ext
  have h1:=oneParticleLorentzUnitary_ae a L (oneParticleSchwartzToHilbert a f)
  have h2:=(lorentzShellMap_preserves_wignerMeasure a L⁻¹).quasiMeasurePreserving.ae
    (f.coeFn_toLp 2 (wignerMeasure a))
  have h3:=(lorentzSchwartzCLM a L f).coeFn_toLp 2 (wignerMeasure a)
  filter_upwards [h1,h2,h3] with p hp hq hr
  exact hp.trans (hq.trans hr.symm)

end AASCKleinGordon
