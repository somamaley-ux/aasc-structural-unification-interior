import WickOneParticleSourcePairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal SchwartzMap
namespace AASCKleinGordon

def wickCovariantScale (a : Parameters) : ℝ := 2*a.mass*a.speed*wickSpatialFourierJacobian a

theorem wick_covariant_scale_positive (a : Parameters) : 0<wickCovariantScale a := by
  have hm := a.mass_pos
  have hc := a.speed_pos
  have hh := a.hbar_pos
  unfold wickCovariantScale
  rw [wick_spatial_fourier_jacobian_value]
  positivity

def wickCovariantMeasure (a : Parameters) : Measure Momentum :=
  ENNReal.ofReal (1/wickCovariantScale a) • wignerMeasure a

abbrev WickCovariantHilbert (a : Parameters) := Lp ℂ 2 (wickCovariantMeasure a)

theorem wick_wigner_eq_scaled_covariant (a : Parameters) :
    wignerMeasure a=ENNReal.ofReal (wickCovariantScale a) • wickCovariantMeasure a := by
  rw [wickCovariantMeasure,smul_smul,← ENNReal.ofReal_mul (wick_covariant_scale_positive a).le]
  simp [(wick_covariant_scale_positive a).ne']

theorem wick_covariant_measure_density (a : Parameters) :
    wickCovariantMeasure a=volume.withDensity
      (fun p => ENNReal.ofReal (1/(2*massShell a p 0*wickSpatialFourierJacobian a))) := by
  rw [wickCovariantMeasure,wignerMeasure,← withDensity_smul _ (wignerDensity_measurable a)]
  congr 1
  funext p
  change ENNReal.ofReal (1/wickCovariantScale a)*ENNReal.ofReal (wignerWeight a p)=_
  rw [← ENNReal.ofReal_mul (one_div_pos.mpr (wick_covariant_scale_positive a)).le]
  congr 1
  have he := (energy_pos a p).ne'
  have hc := a.speed_pos.ne'
  have hj : wickSpatialFourierJacobian a≠0 := by
    rw [wick_spatial_fourier_jacobian_value]
    have hh := a.hbar_pos
    positivity
  dsimp [wickCovariantScale,wignerWeight,massShell]
  field_simp [he,hc,hj,a.mass_pos.ne']
  <;> ring

theorem wick_covariant_ae (a : Parameters) {P : Momentum → Prop} :
    (∀ᵐ p ∂wickCovariantMeasure a,P p) ↔ ∀ᵐ p ∂wignerMeasure a,P p :=
  Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr
    (one_div_pos.mpr (wick_covariant_scale_positive a)))

theorem wick_covariant_integral (a : Parameters) (f : Momentum → ℂ) :
    (∫ p,f p ∂wickCovariantMeasure a)=
      ((1/wickCovariantScale a : ℝ) : ℂ)*(∫ p,f p ∂wignerMeasure a) := by
  rw [wickCovariantMeasure,integral_smul_measure,ENNReal.toReal_ofReal
    (one_div_pos.mpr (wick_covariant_scale_positive a)).le]
  rfl

theorem wick_wigner_double_integral_covariant (a : Parameters) (f : Momentum → Momentum → ℂ) :
    (∫ p,∫ q,f p q ∂wignerMeasure a ∂wignerMeasure a)=
      (wickCovariantScale a : ℂ)^2 *
        ∫ p,∫ q,f p q ∂wickCovariantMeasure a ∂wickCovariantMeasure a := by
  simp_rw [wick_wigner_eq_scaled_covariant a,integral_smul_measure,
    ENNReal.toReal_ofReal (wick_covariant_scale_positive a).le]
  change (wickCovariantScale a : ℂ)*
    (∫ p,(wickCovariantScale a : ℂ)*(∫ q,f p q ∂wickCovariantMeasure a) ∂wickCovariantMeasure a)=_
  rw [integral_const_mul]
  ring

end AASCKleinGordon
