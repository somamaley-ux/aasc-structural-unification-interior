import WickCalibratedSourceRole

noncomputable section
open scoped DirectSum
namespace AASCKleinGordon

/-- -eta(P,P), with contravariant P^0=E/c, on the original common core. -/
def wickOriginalCoreCasimir (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  let P := wickOriginalCoreFourMomentum a
  (P 0).comp (P 0)-((P 1).comp (P 1)+(P 2).comp (P 2)+(P 3).comp (P 3))

theorem wick_original_core_casimir_component (a : Parameters) (v : FiniteParticleCore)
    (n : ℕ) (x : ParticleConfiguration n) :
    (wickOriginalCoreCasimir a v n).val x=
      ((particleFourMomentum a n x 0 : ℂ)^2-(particleFourMomentum a n x 1 : ℂ)^2-
        (particleFourMomentum a n x 2 : ℂ)^2-(particleFourMomentum a n x 3 : ℂ)^2)*(v n).val x := by
  change (wickOriginalCoreFourMomentum a 0 (wickOriginalCoreFourMomentum a 0 v) n).val x-
    ((wickOriginalCoreFourMomentum a 1 (wickOriginalCoreFourMomentum a 1 v) n).val x+
      (wickOriginalCoreFourMomentum a 2 (wickOriginalCoreFourMomentum a 2 v) n).val x+
      (wickOriginalCoreFourMomentum a 3 (wickOriginalCoreFourMomentum a 3 v) n).val x)=_
  simp only [wick_original_core_four_momentum_component]
  ring

theorem wick_original_core_casimir_one_particle (a : Parameters) (f : bosonicSchwartz 1) :
    wickOriginalCoreCasimir a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f)=
      ((a.mass^2*a.speed^2 : ℝ) : ℂ) • DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f := by
  apply DirectSum.ext
  intro n
  apply Subtype.ext
  ext x
  change (wickOriginalCoreCasimir a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f) n).val x=
    ((a.mass^2*a.speed^2 : ℝ) : ℂ)*
      ((DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f) n).val x
  rw [wick_original_core_casimir_component]
  by_cases hn : n=1
  · subst n
    have shell : particleFourMomentum a 1 x=massShell a (x 0) := by
      simp [particleFourMomentum]
    rw [shell]
    have realIdentity : massShell a (x 0) 0^2-massShell a (x 0) 1^2-
        massShell a (x 0) 2^2-massShell a (x 0) 3^2=a.mass^2*a.speed^2 := by
      have h := massShell_on_shell a (x 0)
      dsimp only [minkowskiDot] at h
      nlinarith [h]
    have complexIdentity : (massShell a (x 0) 0 : ℂ)^2-(massShell a (x 0) 1 : ℂ)^2-
        (massShell a (x 0) 2 : ℂ)^2-(massShell a (x 0) 3 : ℂ)^2=
          ((a.mass^2*a.speed^2 : ℝ) : ℂ) := by exact_mod_cast realIdentity
    rw [complexIdentity]
  · have zero : (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f) n=0 := by
      simp [DirectSum.lof_eq_of,DirectSum.of_apply,hn,Ne.symm hn]
    rw [zero]
    simp

/-- This polynomial uses only the SAME actual integrated stress-charge core
operators, after the original generator has determined their calibration. -/
def wickCalibratedStressCasimir (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  let Q := wickOriginalStressChargeCore a (wickPositiveCalibratedAmplitude a)
  (Q 0).comp (Q 0)-((Q 1).comp (Q 1)+(Q 2).comp (Q 2)+(Q 3).comp (Q 3))

theorem wick_calibrated_source_inertial_casimir_same (a : Parameters) :
    wickCalibratedStressCasimir a=wickOriginalCoreCasimir a := by
  simp only [wickCalibratedStressCasimir,wickOriginalCoreCasimir,
    wickOriginalStressChargeCore,wick_positive_calibrated_amplitude_coefficient,one_smul]

theorem wick_calibrated_charge_casimir_one_particle (a : Parameters) (f : bosonicSchwartz 1) :
    wickCalibratedStressCasimir a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f)=
      ((a.mass^2*a.speed^2 : ℝ) : ℂ) • DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1 f := by
  rw [wick_calibrated_source_inertial_casimir_same]
  exact wick_original_core_casimir_one_particle a f

theorem wick_calibrated_charge_casimir_occupied (a : Parameters) :
    oneParticleCore≠0 ∧ wickCalibratedStressCasimir a oneParticleCore=
      ((a.mass^2*a.speed^2 : ℝ) : ℂ) • oneParticleCore :=
  ⟨oneParticleCore_nonzero,wick_calibrated_charge_casimir_one_particle a oneParticleSector⟩

end AASCKleinGordon
