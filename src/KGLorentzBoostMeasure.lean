import KGLorentzBoostJacobian
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AASCKleinGordon

theorem axisBoostMomentum_bijective (a : Parameters) (r : ℝ) :
    Function.Bijective (axisBoostMomentum a r) := by
  constructor
  · exact Function.LeftInverse.injective (axisBoostMomentum_neg_inverse a r)
  · intro p
    refine ⟨axisBoostMomentum a (-r) p, ?_⟩
    simpa only [neg_neg] using axisBoostMomentum_neg_inverse a (-r) p

theorem axisBoostJacobian_continuous (a : Parameters) (r : ℝ) :
    Continuous (axisBoostJacobian a r) :=
  continuous_const.add ((continuous_const.mul (continuous_apply (0 : Fin 3))).div
    (energy_continuous a) (fun p => (energy_pos a p).ne'))

theorem axisBoost_map_jacobian_volume (a : Parameters) (r : ℝ) :
    Measure.map (axisBoostMomentum a r)
      (volume.withDensity (fun p => ENNReal.ofReal (axisBoostJacobian a r p))) =
        (volume : Measure Momentum) := by
  have himage : axisBoostMomentum a r '' Set.univ = Set.univ := by
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr (axisBoostMomentum_bijective a r).2
  have hdet (p : Momentum) : |(axisBoostDerivativeCLM a r p).det| = axisBoostJacobian a r p := by
    rw [axisBoostDerivative_det, abs_of_pos (axisBoostJacobian_pos a r p)]
  have h := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure Momentum)
    (s := Set.univ) (f := axisBoostMomentum a r) (f' := axisBoostDerivativeCLM a r)
    MeasurableSet.univ.nullMeasurableSet
    (fun p _ => (axisBoostMomentum_hasFDerivAt a r p).hasFDerivWithinAt)
    (fun p _ q _ hpq => (axisBoostMomentum_bijective a r).1 hpq)
  simpa only [Measure.restrict_univ, himage, hdet] using h

/-- Weighted change of variables, proved from the actual density Jacobian map. -/
theorem map_weighted_of_jacobian {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → X) (J w : X → ℝ≥0∞) (hF : Measurable F) (hJ : Measurable J)
    (hw : Measurable w) (hmap : Measure.map F (μ.withDensity J) = μ)
    (hweight : ∀ x, w (F x)*J x = w x) :
    Measure.map F (μ.withDensity w) = μ.withDensity w := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hF hs), withDensity_apply _ hs]
  have hlin : (∫⁻ x, J x*(s.indicator w) (F x) ∂μ) = ∫⁻ x, s.indicator w x ∂μ := by
    calc
      _ = ∫⁻ x, (s.indicator w) (F x) ∂μ.withDensity J := by
        simpa only [Pi.mul_apply, Function.comp_apply] using
          (lintegral_withDensity_eq_lintegral_mul μ hJ ((hw.indicator hs).comp hF)).symm
      _ = ∫⁻ x, s.indicator w x ∂Measure.map F (μ.withDensity J) :=
        (lintegral_map (hw.indicator hs) hF).symm
      _ = _ := congrArg (fun ν : Measure X => ∫⁻ x, s.indicator w x ∂ν) hmap
  calc
    _ = ∫⁻ x, (F ⁻¹' s).indicator w x ∂μ := (lintegral_indicator (hF hs) w).symm
    _ = ∫⁻ x, J x*(s.indicator w) (F x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : F x ∈ s
      · simp only [Set.indicator_of_mem (show x ∈ F ⁻¹' s from hx), Set.indicator_of_mem hx]
        exact (hweight x).symm.trans (mul_comm _ _)
      · simp only [Set.indicator_of_notMem (show x ∉ F ⁻¹' s from hx),
          Set.indicator_of_notMem hx, mul_zero]
    _ = _ := hlin
    _ = _ := lintegral_indicator hs w

theorem axisBoostMomentum_preserves_wignerMeasure (a : Parameters) (r : ℝ) :
    MeasurePreserving (axisBoostMomentum a r) (wignerMeasure a) (wignerMeasure a) := by
  have hF : Measurable (axisBoostMomentum a r) :=
    (axisBoostMomentum_temperate a r).1.continuous.measurable
  refine ⟨hF, ?_⟩
  apply map_weighted_of_jacobian volume (axisBoostMomentum a r)
    (fun p => ENNReal.ofReal (axisBoostJacobian a r p)) (wignerDensity a) hF
    (axisBoostJacobian_continuous a r).measurable.ennreal_ofReal (wignerDensity_measurable a)
    (axisBoost_map_jacobian_volume a r)
  intro p
  change ENNReal.ofReal (wignerWeight a (axisBoostMomentum a r p)) *
    ENNReal.ofReal (axisBoostJacobian a r p) = ENNReal.ofReal (wignerWeight a p)
  rw [← ENNReal.ofReal_mul (wignerWeight_pos a _).le, axisBoost_wigner_weight_jacobian]

end AASCKleinGordon
