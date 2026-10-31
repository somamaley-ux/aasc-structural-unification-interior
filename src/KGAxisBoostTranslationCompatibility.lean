import KGSpacetimeTranslationUnitary

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem particleAxisBoost_eventPhase (a : Parameters) (n : ℕ) (r : ℝ) (b : Spacetime)
    (f : ParticleHilbert a n) :
    particleAxisBoostUnitary a n r
      (Multiplication.phaseMultiplier (particleEventMomentum a n b)
        (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)=
      Multiplication.phaseMultiplier (particleEventMomentum a n (spacetimeAxisBoostCLE r b))
        (particleEventMomentum_continuous a n _).measurable a.hbar 1 (particleAxisBoostUnitary a n r f) := by
  apply Lp.ext
  have h1 := particleAxisBoostUnitary_ae a n r
    (Multiplication.phaseMultiplier (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)
  have h2 := (particleAxisBoost_preserves_measure a n (-r)).quasiMeasurePreserving.ae
    (Multiplication.phaseMultiplier_ae (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)
  have h3 := Multiplication.phaseMultiplier_ae (particleEventMomentum a n (spacetimeAxisBoostCLE r b))
    (particleEventMomentum_continuous a n (spacetimeAxisBoostCLE r b)).measurable a.hbar 1 (particleAxisBoostUnitary a n r f)
  have h4 := particleAxisBoostUnitary_ae a n r f
  filter_upwards [h1,h2,h3,h4] with x hx hy hz hw
  rw [hx,hz,hw]
  change (Multiplication.phaseMultiplier (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)
      (particleAxisBoostME a n (-r) x)=
    Translation.phase a.hbar 1 (particleEventMomentum a n (spacetimeAxisBoostCLE r b) x)*
      f (particleAxisBoostME a n (-r) x)
  rw [hy,particleEventMomentum_boost]

theorem fockAxisBoost_eventTranslation (a : Parameters) (r : ℝ) (b : Spacetime)
    (f : FockHilbert a) :
    fockAxisBoostUnitary a r (fockEventTranslation a b f)=
      fockEventTranslation a (spacetimeAxisBoostCLE r b) (fockAxisBoostUnitary a r f) := by
  apply lp.ext
  funext n
  apply Subtype.ext
  exact particleAxisBoost_eventPhase a n r b (f n).val

def fockAxisPoincare (a : Parameters) (b : Spacetime) (r : ℝ) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a :=
  (fockAxisBoostUnitary a r).trans (fockEventTranslation a b)

theorem fockAxisPoincare_mul (a : Parameters) (b d : Spacetime) (r s : ℝ)
    (f : FockHilbert a) :
    fockAxisPoincare a b r (fockAxisPoincare a d s f)=
      fockAxisPoincare a (b+spacetimeAxisBoostCLE r d) (r+s) f := by
  change fockEventTranslation a b (fockAxisBoostUnitary a r
    (fockEventTranslation a d (fockAxisBoostUnitary a s f)))=_
  rw [fockAxisBoost_eventTranslation,← fockEventTranslation_add,fockAxisBoostUnitary_add]
  rfl

theorem fockAxisPoincare_identity (a : Parameters) (f : FockHilbert a) :
    fockAxisPoincare a 0 0 f=f := by
  change fockEventTranslation a 0 (fockAxisBoostUnitary a 0 f)=f
  rw [fockAxisBoostUnitary_zero,fockEventTranslation_zero]

theorem fockAxisPoincare_fixes_vacuum (a : Parameters) (b : Spacetime) (r : ℝ) :
    fockAxisPoincare a b r (fockVacuum a)=fockVacuum a := by
  change fockEventTranslation a b (fockAxisBoostUnitary a r (fockVacuum a))=_
  rw [fockAxisBoost_fixes_original_vacuum,fockEventTranslation_fixes_vacuum]

end AASCKleinGordon
