import KGAxisBoostFieldOperations

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

theorem lp_pullback_composition {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F G H : X → X) (hF : MeasurePreserving F μ μ) (hG : MeasurePreserving G μ μ)
    (hH : MeasurePreserving H μ μ) (hc : ∀ x,G (F x)=H x) (f : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving F hF (Lp.compMeasurePreserving G hG f) =
      Lp.compMeasurePreserving H hH f := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving G hG f) hF
  have h2 := hF.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hG)
  have h3 := Lp.coeFn_compMeasurePreserving f hH
  filter_upwards [h1,h2,h3] with x hx hy hz
  exact (hx.trans hy).trans ((congrArg f (hc x)).trans hz.symm)

theorem lp_pullback_identity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → X) (hF : MeasurePreserving F μ μ) (hi : ∀ x,F x=x) (f : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving F hF f = f := by
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving f hF).mono (fun x hx => hx.trans (congrArg f (hi x)))

theorem particleAxisBoostUnitary_add (a : Parameters) (n : ℕ) (r s : ℝ) (f : ParticleHilbert a n) :
    particleAxisBoostUnitary a n r (particleAxisBoostUnitary a n s f) =
      particleAxisBoostUnitary a n (r+s) f := by
  apply lp_pullback_composition
  intro x
  funext i
  change axisBoostMomentum a (-s) (axisBoostMomentum a (-r) (x i)) =
    axisBoostMomentum a (-(r+s)) (x i)
  rw [← axisBoostMomentum_add]
  congr 1
  ring

theorem particleAxisBoostUnitary_zero (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    particleAxisBoostUnitary a n 0 f = f := by
  apply lp_pullback_identity
  intro x
  funext i
  change axisBoostMomentum a (-0) (x i) = x i
  rw [neg_zero,axisBoostMomentum_zero]

theorem bosonicAxisBoostUnitary_add (a : Parameters) (n : ℕ) (r s : ℝ)
    (f : bosonicHilbertSector a n) :
    bosonicAxisBoostUnitary a n r (bosonicAxisBoostUnitary a n s f) =
      bosonicAxisBoostUnitary a n (r+s) f := by
  apply Subtype.ext
  exact particleAxisBoostUnitary_add a n r s f.val

theorem fockAxisBoostUnitary_add (a : Parameters) (r s : ℝ) (f : FockHilbert a) :
    fockAxisBoostUnitary a r (fockAxisBoostUnitary a s f) = fockAxisBoostUnitary a (r+s) f := by
  apply lp.ext
  funext n
  exact bosonicAxisBoostUnitary_add a n r s (f n)

theorem fockAxisBoostUnitary_zero (a : Parameters) (f : FockHilbert a) :
    fockAxisBoostUnitary a 0 f = f := by
  apply lp.ext
  funext n
  apply Subtype.ext
  exact particleAxisBoostUnitary_zero a n (f n).val

theorem coreAxisBoost_add (a : Parameters) (r s : ℝ) (u : FiniteParticleCore) :
    coreAxisBoost a r (coreAxisBoost a s u) = coreAxisBoost a (r+s) u := by
  apply finiteParticleCoreToFock_injective a
  rw [← fockAxisBoost_intertwines_original_core, ← fockAxisBoost_intertwines_original_core,
    ← fockAxisBoost_intertwines_original_core, fockAxisBoostUnitary_add]

theorem coreAxisBoost_zero (a : Parameters) (u : FiniteParticleCore) : coreAxisBoost a 0 u = u := by
  apply finiteParticleCoreToFock_injective a
  rw [← fockAxisBoost_intertwines_original_core,fockAxisBoostUnitary_zero]

end AASCKleinGordon
