import KGSpacetimeTranslationCoefficients

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem translationPhase_add_value (hbar t v w : ℝ) :
    Translation.phase hbar t (v+w)=Translation.phase hbar t v*Translation.phase hbar t w := by
  unfold Translation.phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem translationPhase_one_mul (hbar t v : ℝ) :
    Translation.phase hbar 1 (t*v)=Translation.phase hbar t v := by
  unfold Translation.phase
  congr 1
  push_cast
  ring

def fockEventTranslation (a : Parameters) (b : Spacetime) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a :=
  fockPhaseUnitary a (fun n => particleEventMomentum a n b)
    (fun n => (particleEventMomentum_continuous a n b).measurable)
    (fun n => particleEventMomentum_permutation a n b) a.hbar 1

theorem fockEventTranslation_add (a : Parameters) (b d : Spacetime) (f : FockHilbert a) :
    fockEventTranslation a (b+d) f=fockEventTranslation a b (fockEventTranslation a d f) := by
  apply lp.ext
  funext n
  apply Subtype.ext
  change Multiplication.phaseMultiplier (particleEventMomentum a n (b+d))
      (particleEventMomentum_continuous a n (b+d)).measurable a.hbar 1 (f n).val=
    Multiplication.phaseMultiplier (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable a.hbar 1
      (Multiplication.phaseMultiplier (particleEventMomentum a n d)
        (particleEventMomentum_continuous a n d).measurable a.hbar 1 (f n).val)
  apply Lp.ext
  filter_upwards [Multiplication.phaseMultiplier_ae (particleEventMomentum a n (b+d)) (particleEventMomentum_continuous a n (b+d)).measurable a.hbar 1 (f n).val,
    Multiplication.phaseMultiplier_ae (particleEventMomentum a n b) (particleEventMomentum_continuous a n b).measurable a.hbar 1
      (Multiplication.phaseMultiplier (particleEventMomentum a n d) (particleEventMomentum_continuous a n d).measurable a.hbar 1 (f n).val),
    Multiplication.phaseMultiplier_ae (particleEventMomentum a n d) (particleEventMomentum_continuous a n d).measurable a.hbar 1 (f n).val]
    with x h1 h2 h3
  rw [h1,h2,h3,particleEventMomentum_add,translationPhase_add_value,mul_assoc]

theorem fockEventTranslation_zero (a : Parameters) (f : FockHilbert a) :
    fockEventTranslation a 0 f=f := by
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Multiplication.phaseMultiplier_ae (particleEventMomentum a n 0) (particleEventMomentum_continuous a n 0).measurable a.hbar 1 (f n).val]
    with x hx
  change (Multiplication.phaseMultiplier (particleEventMomentum a n 0) (particleEventMomentum_continuous a n 0).measurable a.hbar 1 (f n).val) x=(f n).val x
  rw [hx,particleEventMomentum_zero]
  simp [Translation.phase]

theorem fockEventTranslation_inverse (a : Parameters) (b : Spacetime) (f : FockHilbert a) :
    fockEventTranslation a (-b) (fockEventTranslation a b f)=f := by
  rw [← fockEventTranslation_add,neg_add_cancel,fockEventTranslation_zero]

theorem fockPhaseUnitary_eq_of_phase_eq (a : Parameters)
    (v w : ∀ n,ParticleConfiguration n → ℝ)
    (hv : ∀ n,Measurable (v n)) (hw : ∀ n,Measurable (w n))
    (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)
    (hj : ∀ n (σ : Equiv.Perm (Fin n)) x,w n (particlePermutation n σ x)=w n x)
    (hbar t s : ℝ) (he : ∀ n x,Translation.phase hbar t (v n x)=Translation.phase hbar s (w n x))
    (f : FockHilbert a) :
    fockPhaseUnitary a v hv hi hbar t f=fockPhaseUnitary a w hw hj hbar s f := by
  apply lp.ext
  funext n
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [Multiplication.phaseMultiplier_ae (v n) (hv n) hbar t (f n).val,
    Multiplication.phaseMultiplier_ae (w n) (hw n) hbar s (f n).val] with x hx hy
  change (Multiplication.phaseMultiplier (v n) (hv n) hbar t (f n).val) x=
    (Multiplication.phaseMultiplier (w n) (hw n) hbar s (f n).val) x
  rw [hx,hy,he]

theorem fockEventTranslation_time (a : Parameters) (t : ℝ) (f : FockHilbert a) :
    fockEventTranslation a (timeTranslationEvent a t) f=fockTimeTranslation a t f := by
  apply fockPhaseUnitary_eq_of_phase_eq
  intro n x
  have he : particleEventMomentum a n (timeTranslationEvent a t) x=t*particleTotalEnergy a n x := by
    simp only [particleEventMomentum,eventMomentumPair_time,particleTotalEnergy,Finset.mul_sum]
  rw [he,translationPhase_one_mul]

theorem fockEventTranslation_spatial (a : Parameters) (j : Fin 3) (s : ℝ) (f : FockHilbert a) :
    fockEventTranslation a (spatialTranslationEvent j s) f=fockSpatialTranslation a j s f := by
  apply fockPhaseUnitary_eq_of_phase_eq
  intro n x
  have he : particleEventMomentum a n (spatialTranslationEvent j s) x=s*totalMomentumCLM n j x := by
    simp only [particleEventMomentum,eventMomentumPair_spatial,totalMomentumCLM_apply,Finset.mul_sum]
  rw [he,translationPhase_one_mul]

theorem fockEventTranslation_fixes_vacuum (a : Parameters) (b : Spacetime) :
    fockEventTranslation a b (fockVacuum a)=fockVacuum a := by
  apply fockPhaseUnitary_fixes_vacuum
  intro x
  simp [particleEventMomentum]

end AASCKleinGordon
