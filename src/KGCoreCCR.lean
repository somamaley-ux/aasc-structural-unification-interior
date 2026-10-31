import KGBosonicCCR
import KGCoreFieldOperations

noncomputable section
open MeasureTheory
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem mixed_CCR_sector_zero (a : Parameters) (f g : 𝓢(Momentum,ℂ))
    (H : bosonicSchwartz 0) :
    annihilationSectorCLM a 0 f (creationSectorCLM 0 g H) =
      (∫ p, star (f p) * g p ∂wignerMeasure a) • H := by
  apply Subtype.ext
  ext y
  rw [annihilation_creation_sector_apply]
  have hterm (p : Momentum) : (∑ i : Fin (0+1),
      g (Fin.cons (α:=fun _ : Fin (0+1) => Momentum) p y i) *
        H.val (swapDelete 0 i (Fin.cons p y))) = g p * H.val y := by
    rw [Fin.sum_univ_succ]
    simp [swapDelete_zero]
  simp_rw [hterm, ← mul_assoc]
  rw [integral_mul_const]
  rfl

theorem mixed_CCR_core (a : Parameters) (f g : 𝓢(Momentum,ℂ)) :
    (annihilationCore a f).comp (creationCore g) =
      (inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g)) •
        LinearMap.id + (creationCore g).comp (annihilationCore a f) := by
  rw [← test_pair_integral_eq_inner]
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  cases n with
  | zero =>
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, creationCore_lof, annihilationCore_lof_succ,
        annihilationCore_lof_zero, map_zero, add_zero]
      rw [mixed_CCR_sector_zero, map_smul]
  | succ n =>
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, creationCore_lof, annihilationCore_lof_succ]
      rw [mixed_CCR_sector_succ, map_add, map_smul]

set_option maxHeartbeats 1000000 in
theorem mixed_CCR_on_original_fock_core (a : Parameters) (f g : 𝓢(Momentum,ℂ))
    (v : FiniteParticleCore) :
    fockCoreAnnihilation a f (includedFockCore a (creationCore g v)) =
      inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) •
        finiteParticleCoreToFock a v +
      fockCoreCreation a g (includedFockCore a (annihilationCore a f v)) := by
  rw [fockCoreAnnihilation_on_original_core a f (creationCore g v),
    fockCoreCreation_on_original_core a g (annihilationCore a f v)]
  have h := congrArg (fun L : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore => L v)
    (mixed_CCR_core a f g)
  change annihilationCore a f (creationCore g v) =
    inner ℂ (oneParticleSchwartzToHilbert a f) (oneParticleSchwartzToHilbert a g) • v +
      creationCore g (annihilationCore a f v) at h
  rw [h, map_add, map_smul]

theorem creationSector_vacuum_apply (f : 𝓢(Momentum,ℂ)) (p : Momentum) :
    (creationSectorCLM 0 f vacuumSector).val (Fin.cons p Fin.elim0) = f p := by
  rw [creationSectorCLM_apply]
  simp only [Nat.cast_zero, zero_add, Real.sqrt_one, Complex.ofReal_one, one_smul]
  rw [symmetrizer_insert_apply]
  simp [vacuumSector, vacuumSchwartz]

theorem creationCore_vacuum_nonzero (f : 𝓢(Momentum,ℂ)) (hf : f ≠ 0) :
    creationCore f vacuumCore ≠ 0 := by
  intro hz
  apply hf
  ext p
  have h := congrArg (fun v : FiniteParticleCore => (v 1).val (Fin.cons p Fin.elim0)) hz
  have hc : creationCore f vacuumCore = DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) 1
      (creationSectorCLM 0 f vacuumSector) := creationCore_lof f 0 vacuumSector
  rw [hc] at h
  simpa [DirectSum.lof_eq_of, DirectSum.of_apply, creationSector_vacuum_apply] using h

end AASCKleinGordon
