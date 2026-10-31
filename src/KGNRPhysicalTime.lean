import KGNRMomentumContraction
import WickOneParticlePoincare
import KGSpacetimeTranslationCoefficients

/-! The finite-speed multiplier in the contraction is the actual isolated
KG Poincaré time action with its declared homogeneous rest-energy phase removed.
No arbitrary Hilbert-space isomorphism or assumed kinetic certificate enters. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter
namespace AASCKleinGordon

def kgNRCovariantTimeTranslation (a : Parameters) (t : ℝ) :
    WickCovariantHilbert a ≃ₗᵢ[ℂ] WickCovariantHilbert a :=
  wickCovariantPoincareRepresentation a
    ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩

/-- Derived directly from the retained actual isolated Poincaré action and
its proved scalar formula, without importing an unbound matching object. -/
theorem kg_nr_covariant_time_translation_multiplier (a : Parameters) (t : ℝ) :
    kgNRCovariantTimeTranslation a t =
      Multiplication.phaseUnitary (μ := wickCovariantMeasure a) (energy a)
        (energy_continuous a).measurable a.hbar t := by
  apply LinearIsometryEquiv.ext
  intro f
  apply Lp.ext
  filter_upwards [wick_covariant_poincare_scalar_ae a
      ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩ f,
    Multiplication.phaseMultiplier_ae (μ := wickCovariantMeasure a) (energy a)
      (energy_continuous a).measurable a.hbar t f] with p hp hq
  change (wickCovariantPoincareRepresentation a
    ⟨Multiplicative.ofAdd (timeTranslationEvent a t), 1⟩ f) p =
      (Multiplication.phaseMultiplier (μ := wickCovariantMeasure a) (energy a)
        (energy_continuous a).measurable a.hbar t f) p
  rw [hp, hq]
  change Translation.phase a.hbar 1 (eventMomentumPair a (timeTranslationEvent a t) p) *
    f (lorentzShellMap a 1⁻¹ p) = Translation.phase a.hbar t (energy a p) * f p
  simp only [inv_one, lorentzShellMap_one, eventMomentumPair_time]
  congr 1
  simp [Translation.phase, neg_mul]

/-- Actual isolated original Poincaré time evolution, with the homogeneous
rest-energy baseline explicitly removed.  The physical carrier still varies
with the positive speed anchor. -/
def kgNRActualCovariantRestFlow (a : Parameters) (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f : WickCovariantHilbert (kgNRParameters a c hc)) :
    WickCovariantHilbert (kgNRParameters a c hc) :=
  Translation.phase a.hbar t (-a.mass * c ^ 2) •
    kgNRCovariantTimeTranslation (kgNRParameters a c hc) t f

theorem kg_nr_phase_energy_add (hbar t r s : ℝ) :
    Translation.phase hbar t (r + s) =
      Translation.phase hbar t r * Translation.phase hbar t s := by
  rw [Translation.phase, Translation.phase, Translation.phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact finite-speed operator comparison, on the concrete covariant
normalization of the original isolated one-particle sector. -/
theorem kg_nr_actual_covariant_rest_flow_is_multiplier
    (a : Parameters) (c : ℝ) (hc : 0 < c) (t : ℝ)
    (f : WickCovariantHilbert (kgNRParameters a c hc)) :
    kgNRActualCovariantRestFlow a c hc t f =
      Multiplication.phaseMultiplier (μ := wickCovariantMeasure (kgNRParameters a c hc))
        (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t f := by
  apply Lp.ext
  have hU := Multiplication.phaseMultiplier_ae
    (μ := wickCovariantMeasure (kgNRParameters a c hc))
    (energy (kgNRParameters a c hc)) (energy_continuous _).measurable a.hbar t f
  have hK := Multiplication.phaseMultiplier_ae
    (μ := wickCovariantMeasure (kgNRParameters a c hc))
    (kgNRDispersion a c) (kg_nr_dispersion_measurable a c) a.hbar t f
  have hS := Lp.coeFn_smul (Translation.phase a.hbar t (-a.mass * c ^ 2))
    (kgNRCovariantTimeTranslation (kgNRParameters a c hc) t f)
  rw [kg_nr_covariant_time_translation_multiplier] at hS
  filter_upwards [hU, hK, hS] with p hu hk hs
  change (Translation.phase a.hbar t (-a.mass * c ^ 2) •
    kgNRCovariantTimeTranslation (kgNRParameters a c hc) t f) p = _
  rw [kg_nr_covariant_time_translation_multiplier]
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs]
  change Translation.phase a.hbar t (-a.mass * c ^ 2) *
    Multiplication.phaseMultiplier (μ := wickCovariantMeasure (kgNRParameters a c hc))
      (energy (kgNRParameters a c hc)) (energy_continuous _).measurable a.hbar t f p = _
  rw [hu, hk, ← mul_assoc, ← kg_nr_phase_energy_add]
  rw [show -a.mass * c ^ 2 + energy (kgNRParameters a c hc) p =
    energy (kgNRParameters a c hc) p - a.mass * c ^ 2 by ring]
  rw [kg_nr_dispersion_is_rest_subtracted_energy]

/- This module proves an actual Poincaré/energy/rest-phase multiplier equality.
It asserts no new covariant stress-charge graph identity.  Retained calibrated
source-charge closure results continue to have their existing Fock scope. -/

end AASCKleinGordon
