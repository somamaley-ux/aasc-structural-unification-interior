import KGFockTranslationGroups
import KGFockCoreOccupation

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

theorem fockPhaseUnitary_fixes_vacuum (a : Parameters)
    (v : ∀ n,ParticleConfiguration n → ℝ) (hv : ∀ n,Measurable (v n))
    (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x)
    (h0 : ∀ x,v 0 x=0) (hbar t : ℝ) :
    fockPhaseUnitary a v hv hi hbar t (fockVacuum a)=fockVacuum a := by
  change fockPhaseMultiplier a v hv hi hbar t (finiteParticleCoreToFock a vacuumCore)=
    finiteParticleCoreToFock a vacuumCore
  rw [vacuumCore,finiteParticleCoreToFock_on_sector]
  apply lp.ext
  funext n
  change bosonicPhaseMultiplier a n (v n) (hv n) (hi n) hbar t
    (lp.single (E:=fun k : ℕ => bosonicHilbertSector a k) 2 0 (bosonicCoreToSector a 0 vacuumSector) n)=
      lp.single (E:=fun k : ℕ => bosonicHilbertSector a k) 2 0 (bosonicCoreToSector a 0 vacuumSector) n
  by_cases hn : 0=n
  · subst n
    simp only [lp.single_apply,Pi.single_eq_same]
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [Multiplication.phaseMultiplier_ae (v 0) (hv 0) hbar t
      (bosonicCoreToSector a 0 vacuumSector).val] with x hx
    change (Multiplication.phaseMultiplier (v 0) (hv 0) hbar t
      (bosonicCoreToSector a 0 vacuumSector).val) x=_
    rw [hx,h0]
    simp [Translation.phase]
  · simp [lp.single_apply,Pi.single_eq_of_ne' hn,map_zero]

theorem fockSpatialTranslation_fixes_vacuum (a : Parameters) (j : Fin 3) (t : ℝ) :
    fockSpatialTranslation a j t (fockVacuum a)=fockVacuum a :=
  fockPhaseUnitary_fixes_vacuum a _ _ _ (fun x => by simp [totalMomentumCLM_apply]) a.hbar t

theorem fockTimeTranslation_fixes_vacuum (a : Parameters) (t : ℝ) :
    fockTimeTranslation a t (fockVacuum a)=fockVacuum a :=
  fockPhaseUnitary_fixes_vacuum a _ _ _ (fun x => by simp [particleTotalEnergy]) a.hbar t

end AASCKleinGordon
