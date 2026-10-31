import KGGeneralLorentzFieldCovariance
import KGAxisBoostTranslationCompatibility

noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

theorem particleEventMomentum_lorentz (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (b : Spacetime) (x : ParticleConfiguration n) :
    particleEventMomentum a n b (particleLorentzMap a n L⁻¹ x)=
      particleEventMomentum a n (spacetimeLorentzCLE L b) x := by
  unfold particleEventMomentum
  apply Finset.sum_congr rfl
  intro i _
  exact (spacetimeLorentz_inner_shellCovector a L b (x i)).symm

theorem particleLorentz_eventPhase (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (b : Spacetime) (f : ParticleHilbert a n) :
    particleLorentzUnitary a n L
      (Multiplication.phaseMultiplier (particleEventMomentum a n b)
        (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)=
      Multiplication.phaseMultiplier (particleEventMomentum a n (spacetimeLorentzCLE L b))
        (particleEventMomentum_continuous a n _).measurable a.hbar 1 (particleLorentzUnitary a n L f) := by
  apply Lp.ext
  have h1:=particleLorentzUnitary_ae a n L
    (Multiplication.phaseMultiplier (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)
  have h2:=(particleLorentz_preserves_measure a n L⁻¹).quasiMeasurePreserving.ae
    (Multiplication.phaseMultiplier_ae (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1 f)
  have h3:=Multiplication.phaseMultiplier_ae (particleEventMomentum a n (spacetimeLorentzCLE L b))
    (particleEventMomentum_continuous a n _).measurable a.hbar 1 (particleLorentzUnitary a n L f)
  have h4:=particleLorentzUnitary_ae a n L f
  filter_upwards [h1,h2,h3,h4] with x hx hy hz hw
  rw [hx,hz,hw]
  change (Multiplication.phaseMultiplier (particleEventMomentum a n b)
    (particleEventMomentum_continuous a n b).measurable a.hbar 1 f) (particleLorentzME a n L⁻¹ x)=
      Translation.phase a.hbar 1 (particleEventMomentum a n (spacetimeLorentzCLE L b) x)*
        f (particleLorentzME a n L⁻¹ x)
  rw [hy]
  change Translation.phase a.hbar 1 (particleEventMomentum a n b (particleLorentzMap a n L⁻¹ x))*
    f (particleLorentzMap a n L⁻¹ x)=_
  rw [particleEventMomentum_lorentz]
  rfl

theorem fockLorentz_eventTranslation (a : Parameters) (L : ProperLorentzTransform)
    (b : Spacetime) (f : FockHilbert a) :
    fockLorentzUnitary a L (fockEventTranslation a b f)=
      fockEventTranslation a (spacetimeLorentzCLE L b) (fockLorentzUnitary a L f) := by
  apply lp.ext
  funext n
  apply Subtype.ext
  exact particleLorentz_eventPhase a n L b (f n).val

def fockPoincareUnitary (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a := (fockLorentzUnitary a L).trans (fockEventTranslation a b)

theorem fockPoincareUnitary_mul (a : Parameters) (b d : Spacetime) (L M : ProperLorentzTransform)
    (f : FockHilbert a) :
    fockPoincareUnitary a b L (fockPoincareUnitary a d M f)=
      fockPoincareUnitary a (b+spacetimeLorentzCLE L d) (L*M) f := by
  change fockEventTranslation a b (fockLorentzUnitary a L
    (fockEventTranslation a d (fockLorentzUnitary a M f)))=_
  rw [fockLorentz_eventTranslation,← fockEventTranslation_add,fockLorentzUnitary_mul]
  rfl

theorem fockPoincareUnitary_one (a : Parameters) (f : FockHilbert a) : fockPoincareUnitary a 0 1 f=f := by
  change fockEventTranslation a 0 (fockLorentzUnitary a 1 f)=f
  rw [fockLorentzUnitary_one,fockEventTranslation_zero]

theorem fockPoincareUnitary_fixes_vacuum (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    fockPoincareUnitary a b L (fockVacuum a)=fockVacuum a := by
  change fockEventTranslation a b (fockLorentzUnitary a L (fockVacuum a))=_
  rw [fockLorentz_fixes_original_vacuum,fockEventTranslation_fixes_vacuum]

def corePoincare (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform) :
    FiniteParticleCore →ₗ[ℂ] FiniteParticleCore := (coreEventTranslation a b).comp (coreLorentz a L)

theorem fockPoincare_intertwines_original_core (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform)
    (u : FiniteParticleCore) :
    fockPoincareUnitary a b L (finiteParticleCoreToFock a u)=
      finiteParticleCoreToFock a (corePoincare a b L u) := by
  change fockEventTranslation a b (fockLorentzUnitary a L (finiteParticleCoreToFock a u))=_
  rw [fockLorentz_intertwines_original_core,fockEventTranslation_intertwines_original_core]
  rfl

theorem corePoincare_mul (a : Parameters) (b d : Spacetime) (L M : ProperLorentzTransform)
    (u : FiniteParticleCore) :
    corePoincare a b L (corePoincare a d M u)=corePoincare a (b+spacetimeLorentzCLE L d) (L*M) u := by
  apply finiteParticleCoreToFock_injective a
  simp only [← fockPoincare_intertwines_original_core,fockPoincareUnitary_mul]

theorem spacetimeFieldCore_poincare (a : Parameters) (b : Spacetime) (L : ProperLorentzTransform)
    (s : ℝ) (h : 𝓢(Spacetime,ℂ)) (u : FiniteParticleCore) :
    corePoincare a b L (spacetimeFieldCore a s h u)=
      spacetimeFieldCore a s (spacetimeEventTranslationTestCLM b (spacetimeLorentzTestCLM L h))
        (corePoincare a b L u) := by
  change coreEventTranslation a b (coreLorentz a L (spacetimeFieldCore a s h u))=_
  rw [spacetimeFieldCore_lorentz,spacetimeFieldCore_eventTranslation]
  rfl

end AASCKleinGordon
