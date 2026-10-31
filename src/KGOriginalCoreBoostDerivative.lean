import KGAxisBoostHilbertDerivative

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap Topology DirectSum
namespace AASCKleinGordon

theorem particleAxisBoostME_zero (a : Parameters) (n : ℕ) (x : ParticleConfiguration n) :
    particleAxisBoostME a n 0 x = x := by
  funext i
  exact axisBoostMomentum_zero a (x i)

theorem particleAxisBoostDifferential_bosonic (a : Parameters) (n : ℕ) (H : bosonicSchwartz n) :
    particleAxisBoostDifferential a n H.val ∈ bosonicSchwartz n := by
  intro σ x
  have he : (fun r : ℝ => H.val (particleAxisBoostME a n (-r) (fun i => x (σ i)))) =
      (fun r : ℝ => H.val (particleAxisBoostME a n (-r) x)) := by
    funext r
    exact H.property σ (fun i => axisBoostMomentum a (-r) (x i))
  have h1 := particleAxisBoost_schwartz_pointwise_hasDerivAt a n H.val (fun i => x (σ i)) 0
  have h2 := particleAxisBoost_schwartz_pointwise_hasDerivAt a n H.val x 0
  rw [he] at h1
  simpa only [neg_zero,particleAxisBoostME_zero] using h1.unique h2

def sectorAxisBoostDifferential (a : Parameters) (n : ℕ) : bosonicSchwartz n →L[ℂ] bosonicSchwartz n :=
  ((particleAxisBoostDifferential a n).comp (bosonicSchwartz n).subtypeL).codRestrict
    (bosonicSchwartz n) (particleAxisBoostDifferential_bosonic a n)

theorem bosonicAxisBoost_weak_hasDerivAt (a : Parameters) (n : ℕ)
    (H K : bosonicSchwartz n) (r : ℝ) :
    HasDerivAt (fun s => inner ℂ (bosonicCoreToSector a n K)
      (bosonicAxisBoostUnitary a n s (bosonicCoreToSector a n H)))
      (inner ℂ (bosonicCoreToSector a n K)
        (bosonicAxisBoostUnitary a n r (bosonicCoreToSector a n
          (sectorAxisBoostDifferential a n H)))) r :=
  particleAxisBoost_weak_hasDerivAt a n H.val K.val r

theorem bosonicAxisBoost_schwartz_hasDerivAt (a : Parameters) (n : ℕ)
    (H : bosonicSchwartz n) (r : ℝ) :
    HasDerivAt (fun s => bosonicAxisBoostUnitary a n s (bosonicCoreToSector a n H))
      (bosonicAxisBoostUnitary a n r (bosonicCoreToSector a n
        (sectorAxisBoostDifferential a n H))) r :=
  hasDerivAt_of_dense_inner_derivative (bosonicCoreToSector a n)
    (bosonicCoreToSector_dense a n) _ _ (bosonicAxisBoost_strongly_continuous a n _)
    (fun K r => bosonicAxisBoost_weak_hasDerivAt a n H K r) r

def coreAxisBoostDifferential (a : Parameters) : FiniteParticleCore →ₗ[ℂ] FiniteParticleCore :=
  DirectSum.lmap (fun n => (sectorAxisBoostDifferential a n).toLinearMap)

theorem coreAxisBoostDifferential_lof (a : Parameters) (n : ℕ) (H : bosonicSchwartz n) :
    coreAxisBoostDifferential a (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H) =
      DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n (sectorAxisBoostDifferential a n H) := by
  simp only [coreAxisBoostDifferential,DirectSum.lmap_lof]
  rfl

theorem fockAxisBoost_original_core_hasDerivAt (a : Parameters) (u : FiniteParticleCore) (r : ℝ) :
    HasDerivAt (fun s => fockAxisBoostUnitary a s (finiteParticleCoreToFock a u))
      (fockAxisBoostUnitary a r (finiteParticleCoreToFock a (coreAxisBoostDifferential a u))) r := by
  induction u using DirectSum.induction_on with
  | zero =>
      simp only [map_zero]
      exact hasDerivAt_const r 0
  | add x y hx hy =>
      simpa only [map_add] using hx.add hy
  | of n H =>
      change HasDerivAt (fun s => fockAxisBoostUnitary a s (finiteParticleCoreToFock a
        (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)))
          (fockAxisBoostUnitary a r (finiteParticleCoreToFock a (coreAxisBoostDifferential a
            (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n H)))) r
      simp_rw [coreAxisBoostDifferential_lof,finiteParticleCoreToFock_on_sector,fockAxisBoost_on_single]
      exact ((lp.singleContinuousLinearMap ℂ (fun k => bosonicHilbertSector a k) 2 n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r (bosonicAxisBoost_schwartz_hasDerivAt a n H r)

theorem fockAxisBoost_original_core_hasDerivAt_zero (a : Parameters) (u : FiniteParticleCore) :
    HasDerivAt (fun s => fockAxisBoostUnitary a s (finiteParticleCoreToFock a u))
      (finiteParticleCoreToFock a (coreAxisBoostDifferential a u)) 0 := by
  simpa only [fockAxisBoostUnitary_zero] using fockAxisBoost_original_core_hasDerivAt a u 0

end AASCKleinGordon
