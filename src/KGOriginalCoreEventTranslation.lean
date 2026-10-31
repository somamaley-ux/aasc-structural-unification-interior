import KGEventTranslationSchwartz
import KGOriginalCoreAxisBoost

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

def bosonicEventTranslationSchwartzCLM (a : Parameters) (n : ℕ) (b : Spacetime) :
    bosonicSchwartz n →L[ℂ] bosonicSchwartz n :=
  ((particleEventTranslationSchwartzCLM a n b).comp (bosonicSchwartz n).subtypeL).codRestrict
    (bosonicSchwartz n) (fun H => by
      intro σ x
      change particleEventTranslationSchwartzCLM a n b H.val (fun i => x (σ i))=
        particleEventTranslationSchwartzCLM a n b H.val x
      rw [particleEventTranslationSchwartz_apply,particleEventTranslationSchwartz_apply,H.property]
      have hp := particleEventTranslationPhase_permutation a n b σ.symm x
      have he : particlePermutation n σ.symm x=(fun i => x (σ i)) := by
        ext i
        simp only [particlePermutation_apply,Equiv.symm_symm]
      rw [he] at hp
      exact congrArg (fun c : ℂ => c*H.val x) hp)

theorem bosonicEventTranslationSchwartz_apply (a : Parameters) (n : ℕ) (b : Spacetime)
    (H : bosonicSchwartz n) (x : ParticleConfiguration n) :
    (bosonicEventTranslationSchwartzCLM a n b H).val x=particleEventTranslationPhase a n b x*H.val x :=
  particleEventTranslationSchwartz_apply a n b H.val x

theorem particleEventTranslation_intertwines_schwartz (a : Parameters) (n : ℕ) (b : Spacetime)
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    Multiplication.phaseMultiplier (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable a.hbar 1 (particleSchwartzToHilbert a n H)=
      particleSchwartzToHilbert a n (particleEventTranslationSchwartzCLM a n b H) := by
  apply Lp.ext
  have h1 := Multiplication.phaseMultiplier_ae (particleEventMomentum a n b)
    (particleEventMomentum_continuous a n b).measurable a.hbar 1 (particleSchwartzToHilbert a n H)
  have h2 := H.coeFn_toLp 2 (particleMeasure a n)
  have h3 := (particleEventTranslationSchwartzCLM a n b H).coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2,h3] with x hx hy hz
  change (Multiplication.phaseMultiplier (particleEventMomentum a n b)
    (particleEventMomentum_continuous a n b).measurable a.hbar 1 (H.toLp 2 (particleMeasure a n))) x=
      Translation.phase a.hbar 1 (particleEventMomentum a n b x)*(H.toLp 2 (particleMeasure a n)) x at hx
  change (Multiplication.phaseMultiplier (particleEventMomentum a n b)
    (particleEventMomentum_continuous a n b).measurable a.hbar 1 (H.toLp 2 (particleMeasure a n))) x=
      ((particleEventTranslationSchwartzCLM a n b H).toLp 2 (particleMeasure a n)) x
  rw [hx,hy,hz,particleEventTranslationSchwartz_apply]
  rfl

theorem bosonicEventTranslation_intertwines_original_schwartz (a : Parameters) (n : ℕ) (b : Spacetime)
    (H : bosonicSchwartz n) :
    bosonicPhaseMultiplier a n (particleEventMomentum a n b)
      (particleEventMomentum_continuous a n b).measurable (particleEventMomentum_permutation a n b)
      a.hbar 1 (bosonicCoreToSector a n H)=
      bosonicCoreToSector a n (bosonicEventTranslationSchwartzCLM a n b H) := by
  apply Subtype.ext
  exact particleEventTranslation_intertwines_schwartz a n b H.val

def coreEventTranslation (a : Parameters) (b : Spacetime) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => (bosonicEventTranslationSchwartzCLM a n b).toLinearMap)

theorem coreEventTranslation_lof (a : Parameters) (b : Spacetime) (n : ℕ) (H : bosonicSchwartz n) :
    coreEventTranslation a b (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)=
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (bosonicEventTranslationSchwartzCLM a n b H) := by
  simp only [coreEventTranslation,DirectSum.lmap_lof]
  rfl

theorem coreEventTranslation_continuous (a : Parameters) (b : Spacetime) :
    Continuous (coreEventTranslation a b) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  change Continuous (fun H : bosonicSchwartz n => coreEventTranslation a b
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp_rw [coreEventTranslation_lof]
  exact (finiteParticleCore_lof_continuous n).comp (bosonicEventTranslationSchwartzCLM a n b).continuous

theorem fockEventTranslation_on_single (a : Parameters) (b : Spacetime) (n : ℕ)
    (H : bosonicHilbertSector a n) :
    fockEventTranslation a b (lp.single 2 n H)=
      lp.single 2 n (bosonicPhaseMultiplier a n (particleEventMomentum a n b)
        (particleEventMomentum_continuous a n b).measurable (particleEventMomentum_permutation a n b)
        a.hbar 1 H) := by
  apply lp.ext
  funext m
  change bosonicPhaseMultiplier a m (particleEventMomentum a m b)
      (particleEventMomentum_continuous a m b).measurable (particleEventMomentum_permutation a m b)
      a.hbar 1 (lp.single (E := fun k => bosonicHilbertSector a k) 2 n H m)=_
  by_cases h : n=m
  · subst m
    simp only [lp.single_apply,Pi.single_eq_same]
  · simp [lp.single_apply,Ne.symm h,map_zero]

theorem fockEventTranslation_intertwines_original_core (a : Parameters) (b : Spacetime)
    (u : FiniteParticleCore) :
    fockEventTranslation a b (finiteParticleCoreToFock a u)=
      finiteParticleCoreToFock a (coreEventTranslation a b u) := by
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
    change fockEventTranslation a b (finiteParticleCoreToFock a
      (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))=
      finiteParticleCoreToFock a (coreEventTranslation a b
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
    rw [coreEventTranslation_lof,finiteParticleCoreToFock_on_sector,
      finiteParticleCoreToFock_on_sector,fockEventTranslation_on_single,
      bosonicEventTranslation_intertwines_original_schwartz]

theorem fockEventTranslation_preserves_original_domain (a : Parameters) (b : Spacetime)
    (u : fockCoreDomain a) : fockEventTranslation a b u.val ∈ fockCoreDomain a := by
  obtain ⟨v,hv⟩ := u.property
  rw [← hv,fockEventTranslation_intertwines_original_core]
  exact ⟨coreEventTranslation a b v,rfl⟩

theorem coreEventTranslation_add (a : Parameters) (b d : Spacetime) (u : FiniteParticleCore) :
    coreEventTranslation a (b+d) u=coreEventTranslation a b (coreEventTranslation a d u) := by
  apply finiteParticleCoreToFock_injective a
  simp only [← fockEventTranslation_intertwines_original_core,fockEventTranslation_add]

theorem coreEventTranslation_zero (a : Parameters) (u : FiniteParticleCore) :
    coreEventTranslation a 0 u=u := by
  apply finiteParticleCoreToFock_injective a
  rw [← fockEventTranslation_intertwines_original_core,fockEventTranslation_zero]

theorem coreEventTranslation_inverse (a : Parameters) (b : Spacetime) (u : FiniteParticleCore) :
    coreEventTranslation a (-b) (coreEventTranslation a b u)=u := by
  rw [← coreEventTranslation_add,neg_add_cancel,coreEventTranslation_zero]

theorem coreEventTranslation_preserves_inner (a : Parameters) (b : Spacetime) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (coreEventTranslation a b u))
      (finiteParticleCoreToFock a (coreEventTranslation a b v))=
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v) := by
  rw [← fockEventTranslation_intertwines_original_core,← fockEventTranslation_intertwines_original_core]
  exact (fockEventTranslation a b).inner_map_map _ _

end AASCKleinGordon
