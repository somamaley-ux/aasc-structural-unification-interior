import KGOriginalCoreAxisBoost
import KGBosonicInsertionFormula
import KGFockCoreAdjointness

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem bosonicAxisBoostSchwartz_inverse (a : Parameters) (n : ℕ) (r : ℝ)
    (H : bosonicSchwartz n) :
    bosonicAxisBoostSchwartzCLM a n (-r) (bosonicAxisBoostSchwartzCLM a n r H) = H := by
  apply Subtype.ext
  ext x
  change H.val (fun i => axisBoostMomentum a (-r) (axisBoostMomentum a (-(-r)) (x i))) = H.val x
  simp only [neg_neg, axisBoostMomentum_neg_inverse]

theorem coreAxisBoost_inverse (a : Parameters) (r : ℝ) (u : FiniteParticleCore) :
    coreAxisBoost a (-r) (coreAxisBoost a r u) = u := by
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
      change coreAxisBoost a (-r) (coreAxisBoost a r
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)) = _
      rw [coreAxisBoost_lof,coreAxisBoost_lof,bosonicAxisBoostSchwartz_inverse]
      rfl

theorem coreAxisBoost_preserves_inner (a : Parameters) (r : ℝ) (u v : FiniteParticleCore) :
    inner ℂ (finiteParticleCoreToFock a (coreAxisBoost a r u))
      (finiteParticleCoreToFock a (coreAxisBoost a r v)) =
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a v) := by
  rw [← fockAxisBoost_intertwines_original_core, ← fockAxisBoost_intertwines_original_core]
  exact (fockAxisBoostUnitary a r).inner_map_map _ _

theorem axisBoost_creationSector (a : Parameters) (n : ℕ) (r : ℝ)
    (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    bosonicAxisBoostSchwartzCLM a (n+1) r (creationSectorCLM n f H) =
      creationSectorCLM n (axisBoostSchwartzCLM a r f) (bosonicAxisBoostSchwartzCLM a n r H) := by
  apply Subtype.ext
  ext y
  change (creationSectorCLM n f H).val (fun i => axisBoostMomentum a (-r) (y i)) =
    (creationSectorCLM n (axisBoostSchwartzCLM a r f)
      (bosonicAxisBoostSchwartzCLM a n r H)).val y
  simp only [creationSectorCLM_apply,SchwartzMap.smul_apply,smul_eq_mul,symmetrizer_insert_apply,
    axisBoostSchwartzCLM_apply]
  rfl

theorem axisBoost_creationCore (a : Parameters) (r : ℝ) (f : 𝓢(Momentum,ℂ))
    (u : FiniteParticleCore) :
    coreAxisBoost a r (creationCore f u) =
      creationCore (axisBoostSchwartzCLM a r f) (coreAxisBoost a r u) := by
  induction u using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of n H =>
      change coreAxisBoost a r (creationCore f
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)) =
        creationCore (axisBoostSchwartzCLM a r f) (coreAxisBoost a r
          (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
      rw [creationCore_lof,coreAxisBoost_lof,coreAxisBoost_lof,creationCore_lof,axisBoost_creationSector]

theorem original_core_inner_ext (a : Parameters) (u v : FiniteParticleCore)
    (h : ∀ w, inner ℂ (finiteParticleCoreToFock a w) (finiteParticleCoreToFock a u) =
      inner ℂ (finiteParticleCoreToFock a w) (finiteParticleCoreToFock a v)) : u = v := by
  have hd : inner ℂ (finiteParticleCoreToFock a (u-v)) (finiteParticleCoreToFock a (u-v)) = 0 := by
    rw [map_sub (finiteParticleCoreToFock a) u v, inner_sub_right]
    exact sub_eq_zero.mpr (by simpa only [map_sub] using h (u-v))
  apply sub_eq_zero.mp
  apply finiteParticleCoreToFock_injective a
  exact (inner_self_eq_zero.mp hd).trans (map_zero _).symm

theorem axisBoost_annihilationCore (a : Parameters) (r : ℝ) (f : 𝓢(Momentum,ℂ))
    (v : FiniteParticleCore) :
    coreAxisBoost a r (annihilationCore a f v) =
      annihilationCore a (axisBoostSchwartzCLM a r f) (coreAxisBoost a r v) := by
  apply original_core_inner_ext a
  intro w
  let u := coreAxisBoost a (-r) w
  have hu : coreAxisBoost a r u = w := by
    simpa only [u,neg_neg] using coreAxisBoost_inverse a (-r) w
  calc
    inner ℂ (finiteParticleCoreToFock a w)
        (finiteParticleCoreToFock a (coreAxisBoost a r (annihilationCore a f v))) =
      inner ℂ (finiteParticleCoreToFock a u) (finiteParticleCoreToFock a (annihilationCore a f v)) := by
        rw [← hu,coreAxisBoost_preserves_inner]
    _ = inner ℂ (finiteParticleCoreToFock a (creationCore f u))
        (finiteParticleCoreToFock a v) := (creation_annihilation_original_core_inner a f u v).symm
    _ = inner ℂ (finiteParticleCoreToFock a (coreAxisBoost a r (creationCore f u)))
        (finiteParticleCoreToFock a (coreAxisBoost a r v)) := (coreAxisBoost_preserves_inner a r _ _).symm
    _ = inner ℂ (finiteParticleCoreToFock a w)
        (finiteParticleCoreToFock a (annihilationCore a (axisBoostSchwartzCLM a r f)
          (coreAxisBoost a r v))) := by
        rw [axisBoost_creationCore,creation_annihilation_original_core_inner,hu]

end AASCKleinGordon
