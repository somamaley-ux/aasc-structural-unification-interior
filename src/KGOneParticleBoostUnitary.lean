import KGLorentzBoostMeasure
import LpMeasureEquivalence

noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

def axisBoostMomentumME (a : Parameters) (r : ℝ) : Momentum ≃ᵐ Momentum where
  toEquiv :=
    { toFun := axisBoostMomentum a r
      invFun := axisBoostMomentum a (-r)
      left_inv := axisBoostMomentum_neg_inverse a r
      right_inv := by intro p; simpa only [neg_neg] using axisBoostMomentum_neg_inverse a (-r) p }
  measurable_toFun := (axisBoostMomentum_temperate a r).1.continuous.measurable
  measurable_invFun := (axisBoostMomentum_temperate a (-r)).1.continuous.measurable

def oneParticleBoostUnitary (a : Parameters) (r : ℝ) :
    OneParticleHilbert a ≃ₗᵢ[ℂ] OneParticleHilbert a :=
  lpMeasureEquivalence (axisBoostMomentumME a (-r))
    (axisBoostMomentum_preserves_wignerMeasure a (-r))
    (MeasurePreserving.symm (axisBoostMomentumME a (-r))
      (axisBoostMomentum_preserves_wignerMeasure a (-r)))

theorem oneParticleBoostUnitary_ae (a : Parameters) (r : ℝ) (f : OneParticleHilbert a) :
    (oneParticleBoostUnitary a r f : Momentum → ℂ) =ᵐ[wignerMeasure a]
      (fun p => f (axisBoostMomentum a (-r) p)) :=
  Lp.coeFn_compMeasurePreserving f (axisBoostMomentum_preserves_wignerMeasure a (-r))

theorem oneParticleBoostUnitary_intertwines_original_schwartz (a : Parameters) (r : ℝ)
    (f : 𝓢(Momentum,ℂ)) :
    oneParticleBoostUnitary a r (oneParticleSchwartzToHilbert a f) =
      oneParticleSchwartzToHilbert a (axisBoostSchwartzCLM a r f) := by
  apply Lp.ext
  have h1 := oneParticleBoostUnitary_ae a r (oneParticleSchwartzToHilbert a f)
  have h2 := (axisBoostMomentum_preserves_wignerMeasure a (-r)).quasiMeasurePreserving.ae
    (f.coeFn_toLp 2 (wignerMeasure a))
  have h3 := (axisBoostSchwartzCLM a r f).coeFn_toLp 2 (wignerMeasure a)
  filter_upwards [h1,h2,h3] with p hp hq hr
  exact hp.trans (hq.trans hr.symm)

theorem lp_comp_commute {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F G : X → X) (hF : MeasurePreserving F μ μ) (hG : MeasurePreserving G μ μ)
    (hc : ∀ x, F (G x) = G (F x)) (f : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving F hF (Lp.compMeasurePreserving G hG f) =
      Lp.compMeasurePreserving G hG (Lp.compMeasurePreserving F hF f) := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving G hG f) hF
  have h2 := hF.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hG)
  have h3 := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving F hF f) hG
  have h4 := hG.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hF)
  filter_upwards [h1,h2,h3,h4] with x hx hy hz hw
  exact (hx.trans hy).trans ((congrArg f (hc x).symm).trans (hz.trans hw).symm)

end AASCKleinGordon
