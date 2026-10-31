import KGGeneralLorentzFockUnitary
import KGGeneralLorentzCreation
import KGAxisBoostGroup

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem particleLorentz_intertwines_schwartz (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    particleLorentzUnitary a n L (particleSchwartzToHilbert a n H) =
      particleSchwartzToHilbert a n (particleLorentzSchwartzCLM a n L H) := by
  apply Lp.ext
  have h1 := particleLorentzUnitary_ae a n L (particleSchwartzToHilbert a n H)
  have h2 := (particleLorentz_preserves_measure a n (L⁻¹)).quasiMeasurePreserving.ae
    (H.coeFn_toLp 2 (particleMeasure a n))
  have h3 := (particleLorentzSchwartzCLM a n L H).coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2,h3] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

theorem bosonicLorentz_intertwines_original_schwartz (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (H : bosonicSchwartz n) :
    bosonicLorentzUnitary a n L (bosonicCoreToSector a n H) =
      bosonicCoreToSector a n (bosonicLorentzSchwartzCLM a n L H) := by
  apply Subtype.ext
  exact particleLorentz_intertwines_schwartz a n L H.val

theorem fockLorentz_on_single (a : Parameters) (L : ProperLorentzTransform) (n : ℕ) (H : bosonicHilbertSector a n) :
    fockLorentzUnitary a L (lp.single 2 n H) =
      lp.single 2 n (bosonicLorentzUnitary a n L H) := by
  apply lp.ext
  funext m
  change bosonicLorentzUnitary a m L (lp.single (E := fun k => bosonicHilbertSector a k) 2 n H m) =
    lp.single (E := fun k => bosonicHilbertSector a k) 2 n (bosonicLorentzUnitary a n L H) m
  by_cases h : n = m
  · subst m
    simp only [lp.single_apply, Pi.single_eq_same]
  · simp [lp.single_apply, Ne.symm h, map_zero]

theorem fockLorentz_intertwines_original_core (a : Parameters) (L : ProperLorentzTransform) (v : FiniteParticleCore) :
    fockLorentzUnitary a L (finiteParticleCoreToFock a v) =
      finiteParticleCoreToFock a (coreLorentz a L v) := by
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n H =>
      change fockLorentzUnitary a L (finiteParticleCoreToFock a
          (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)) =
        finiteParticleCoreToFock a (coreLorentz a L
          (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
      rw [coreLorentz_lof, finiteParticleCoreToFock_on_sector,
        finiteParticleCoreToFock_on_sector, fockLorentz_on_single,
        bosonicLorentz_intertwines_original_schwartz]

theorem fockLorentz_preserves_original_domain (a : Parameters) (L : ProperLorentzTransform)
    (v : fockCoreDomain a) : fockLorentzUnitary a L v.val ∈ fockCoreDomain a := by
  obtain ⟨u,hu⟩ := v.property
  rw [← hu, fockLorentz_intertwines_original_core]
  exact ⟨coreLorentz a L u,rfl⟩

theorem fockLorentz_fixes_original_vacuum (a : Parameters) (L : ProperLorentzTransform) :
    fockLorentzUnitary a L (fockVacuum a) = fockVacuum a := by
  rw [fockVacuum, fockLorentz_intertwines_original_core]
  congr 1
  rw [vacuumCore, coreLorentz_lof]
  congr 1


theorem coreLorentz_preserves_inner (a : Parameters) (L : ProperLorentzTransform)
    (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (coreLorentz a L u))
      (finiteParticleCoreToFock a (coreLorentz a L v))=
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v) := by
  rw [← fockLorentz_intertwines_original_core,← fockLorentz_intertwines_original_core]
  exact (fockLorentzUnitary a L).inner_map_map _ _

theorem particleLorentzUnitary_mul (a : Parameters) (n : ℕ) (L M : ProperLorentzTransform)
    (f : ParticleHilbert a n) :
    particleLorentzUnitary a n L (particleLorentzUnitary a n M f)=
      particleLorentzUnitary a n (L*M) f := by
  apply lp_pullback_composition
  intro x
  change particleLorentzMap a n M⁻¹ (particleLorentzMap a n L⁻¹ x)=
    particleLorentzMap a n (L*M)⁻¹ x
  rw [mul_inv_rev,particleLorentzMap_mul]

theorem particleLorentzUnitary_one (a : Parameters) (n : ℕ) (f : ParticleHilbert a n) :
    particleLorentzUnitary a n 1 f=f := by
  apply lp_pullback_identity
  intro x
  change particleLorentzMap a n (1 : ProperLorentzTransform)⁻¹ x=x
  rw [inv_one,particleLorentzMap_one]

theorem fockLorentzUnitary_mul (a : Parameters) (L M : ProperLorentzTransform) (f : FockHilbert a) :
    fockLorentzUnitary a L (fockLorentzUnitary a M f)=fockLorentzUnitary a (L*M) f := by
  apply lp.ext
  funext n
  apply Subtype.ext
  exact particleLorentzUnitary_mul a n L M (f n).val

theorem fockLorentzUnitary_one (a : Parameters) (f : FockHilbert a) : fockLorentzUnitary a 1 f=f := by
  apply lp.ext
  funext n
  apply Subtype.ext
  exact particleLorentzUnitary_one a n (f n).val

end AASCKleinGordon
