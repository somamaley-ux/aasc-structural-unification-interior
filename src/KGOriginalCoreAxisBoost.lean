import KGFockAxisBoostUnitary
import KGCoreTopologyRepresentation

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem particleAxisBoost_temperate (a : Parameters) (n : ℕ) (r : ℝ) :
    (fun x : ParticleConfiguration n => particleAxisBoostME a n r x).HasTemperateGrowth := by
  classical
  have h : (fun x : ParticleConfiguration n => ∑ i : Fin n,
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => Momentum) i)
        (axisBoostMomentum a r (x i))).HasTemperateGrowth := by
    apply Function.HasTemperateGrowth.sum
    intro i _
    exact (ContinuousLinearMap.single ℝ (fun _ : Fin n => Momentum) i).hasTemperateGrowth.comp
      ((axisBoostMomentum_temperate a r).comp
        (ContinuousLinearMap.proj i : ParticleConfiguration n →L[ℝ] Momentum).hasTemperateGrowth)
  convert h using 1
  funext x i
  simp [ContinuousLinearMap.single_apply]
  rfl

theorem particleAxisBoost_inverse (a : Parameters) (n : ℕ) (r : ℝ) (x : ParticleConfiguration n) :
    particleAxisBoostME a n (-r) (particleAxisBoostME a n r x) = x :=
  (particleAxisBoostME a n r).symm_apply_apply x

theorem particleAxisBoost_polynomial_inverse_bound (a : Parameters) (n : ℕ) (r : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C*(1+‖particleAxisBoostME a n r x‖)^k := by
  obtain ⟨k,C,h⟩ := (particleAxisBoost_temperate a n (-r)).2 0
  refine ⟨k,C,fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_zero, particleAxisBoost_inverse] using h (particleAxisBoostME a n r x)

def particleAxisBoostSchwartzCLM (a : Parameters) (n : ℕ) (r : ℝ) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.compCLM ℂ (particleAxisBoost_temperate a n (-r))
    (particleAxisBoost_polynomial_inverse_bound a n (-r))

@[simp] theorem particleAxisBoostSchwartzCLM_apply (a : Parameters) (n : ℕ) (r : ℝ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    particleAxisBoostSchwartzCLM a n r H x = H (particleAxisBoostME a n (-r) x) := rfl

def bosonicAxisBoostSchwartzCLM (a : Parameters) (n : ℕ) (r : ℝ) :
    bosonicSchwartz n →L[ℂ] bosonicSchwartz n :=
  ((particleAxisBoostSchwartzCLM a n r).comp (bosonicSchwartz n).subtypeL).codRestrict
    (bosonicSchwartz n) (fun H => by
      intro σ x
      change H.val (fun i => axisBoostMomentum a (-r) (x (σ i))) =
        H.val (fun i => axisBoostMomentum a (-r) (x i))
      exact H.property σ (fun i => axisBoostMomentum a (-r) (x i)))

theorem particleAxisBoost_intertwines_schwartz (a : Parameters) (n : ℕ) (r : ℝ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    particleAxisBoostUnitary a n r (particleSchwartzToHilbert a n H) =
      particleSchwartzToHilbert a n (particleAxisBoostSchwartzCLM a n r H) := by
  apply Lp.ext
  have h1 := particleAxisBoostUnitary_ae a n r (particleSchwartzToHilbert a n H)
  have h2 := (particleAxisBoost_preserves_measure a n (-r)).quasiMeasurePreserving.ae
    (H.coeFn_toLp 2 (particleMeasure a n))
  have h3 := (particleAxisBoostSchwartzCLM a n r H).coeFn_toLp 2 (particleMeasure a n)
  filter_upwards [h1,h2,h3] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

theorem bosonicAxisBoost_intertwines_original_schwartz (a : Parameters) (n : ℕ) (r : ℝ)
    (H : bosonicSchwartz n) :
    bosonicAxisBoostUnitary a n r (bosonicCoreToSector a n H) =
      bosonicCoreToSector a n (bosonicAxisBoostSchwartzCLM a n r H) := by
  apply Subtype.ext
  exact particleAxisBoost_intertwines_schwartz a n r H.val

def coreAxisBoost (a : Parameters) (r : ℝ) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => (bosonicAxisBoostSchwartzCLM a n r).toLinearMap)

@[simp] theorem coreAxisBoost_lof (a : Parameters) (r : ℝ) (n : ℕ) (H : bosonicSchwartz n) :
    coreAxisBoost a r (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H) =
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (bosonicAxisBoostSchwartzCLM a n r H) := by
  simp only [coreAxisBoost, DirectSum.lmap_lof]
  rfl

theorem coreAxisBoost_continuous (a : Parameters) (r : ℝ) : Continuous (coreAxisBoost a r) := by
  apply (core_linearMap_continuous_iff _ finiteParticleCore_withSeminorms _).mpr
  intro n
  change Continuous (fun H : bosonicSchwartz n => coreAxisBoost a r
    (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
  simp_rw [coreAxisBoost_lof]
  exact (finiteParticleCore_lof_continuous n).comp (bosonicAxisBoostSchwartzCLM a n r).continuous

theorem fockAxisBoost_on_single (a : Parameters) (r : ℝ) (n : ℕ) (H : bosonicHilbertSector a n) :
    fockAxisBoostUnitary a r (lp.single 2 n H) =
      lp.single 2 n (bosonicAxisBoostUnitary a n r H) := by
  apply lp.ext
  funext m
  change bosonicAxisBoostUnitary a m r (lp.single (E := fun k => bosonicHilbertSector a k) 2 n H m) =
    lp.single (E := fun k => bosonicHilbertSector a k) 2 n (bosonicAxisBoostUnitary a n r H) m
  by_cases h : n = m
  · subst m
    simp only [lp.single_apply, Pi.single_eq_same]
  · simp [lp.single_apply, Ne.symm h, map_zero]

theorem fockAxisBoost_intertwines_original_core (a : Parameters) (r : ℝ) (v : FiniteParticleCore) :
    fockAxisBoostUnitary a r (finiteParticleCoreToFock a v) =
      finiteParticleCoreToFock a (coreAxisBoost a r v) := by
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n H =>
      change fockAxisBoostUnitary a r (finiteParticleCoreToFock a
          (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)) =
        finiteParticleCoreToFock a (coreAxisBoost a r
          (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H))
      rw [coreAxisBoost_lof, finiteParticleCoreToFock_on_sector,
        finiteParticleCoreToFock_on_sector, fockAxisBoost_on_single,
        bosonicAxisBoost_intertwines_original_schwartz]

theorem fockAxisBoost_preserves_original_domain (a : Parameters) (r : ℝ)
    (v : fockCoreDomain a) : fockAxisBoostUnitary a r v.val ∈ fockCoreDomain a := by
  obtain ⟨u,hu⟩ := v.property
  rw [← hu, fockAxisBoost_intertwines_original_core]
  exact ⟨coreAxisBoost a r u,rfl⟩

theorem fockAxisBoost_fixes_original_vacuum (a : Parameters) (r : ℝ) :
    fockAxisBoostUnitary a r (fockVacuum a) = fockVacuum a := by
  rw [fockVacuum, fockAxisBoost_intertwines_original_core]
  congr 1
  rw [vacuumCore, coreAxisBoost_lof]
  congr 1

end AASCKleinGordon
