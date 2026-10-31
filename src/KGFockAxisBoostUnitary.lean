import KGOneParticleBoostUnitary
import KGFockBoundedMultipliers

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

def particleAxisBoostME (a : Parameters) (n : ℕ) (r : ℝ) :
    ParticleConfiguration n ≃ᵐ ParticleConfiguration n where
  toEquiv :=
    { toFun := fun x i => axisBoostMomentum a r (x i)
      invFun := fun x i => axisBoostMomentum a (-r) (x i)
      left_inv := fun x => funext (fun i => axisBoostMomentum_neg_inverse a r (x i))
      right_inv := fun x => funext (fun i => by
        simpa only [neg_neg] using axisBoostMomentum_neg_inverse a (-r) (x i)) }
  measurable_toFun := measurable_pi_iff.mpr (fun i =>
    (axisBoostMomentumME a r).measurable.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.mpr (fun i =>
    (axisBoostMomentumME a (-r)).measurable.comp (measurable_pi_apply i))

theorem particleAxisBoost_preserves_measure (a : Parameters) (n : ℕ) (r : ℝ) :
    MeasurePreserving (particleAxisBoostME a n r) (particleMeasure a n) (particleMeasure a n) :=
  measurePreserving_pi (fun _ : Fin n => wignerMeasure a) (fun _ => wignerMeasure a)
    (fun _ => axisBoostMomentum_preserves_wignerMeasure a r)

def particleAxisBoostUnitary (a : Parameters) (n : ℕ) (r : ℝ) :
    ParticleHilbert a n ≃ₗᵢ[ℂ] ParticleHilbert a n :=
  lpMeasureEquivalence (particleAxisBoostME a n (-r))
    (particleAxisBoost_preserves_measure a n (-r))
    (MeasurePreserving.symm (particleAxisBoostME a n (-r))
      (particleAxisBoost_preserves_measure a n (-r)))

theorem particleAxisBoostUnitary_ae (a : Parameters) (n : ℕ) (r : ℝ) (f : ParticleHilbert a n) :
    (particleAxisBoostUnitary a n r f : ParticleConfiguration n → ℂ) =ᵐ[particleMeasure a n]
      (fun x => f (fun i => axisBoostMomentum a (-r) (x i))) :=
  Lp.coeFn_compMeasurePreserving f (particleAxisBoost_preserves_measure a n (-r))

theorem particleAxisBoostUnitary_symm (a : Parameters) (n : ℕ) (r : ℝ)
    (f : ParticleHilbert a n) :
    (particleAxisBoostUnitary a n r).symm f = particleAxisBoostUnitary a n (-r) f := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving f
    (MeasurePreserving.symm (particleAxisBoostME a n (-r))
      (particleAxisBoost_preserves_measure a n (-r)))
  have h2 := particleAxisBoostUnitary_ae a n (-r) f
  filter_upwards [h1,h2] with x hx hy
  exact hx.trans hy.symm

theorem particleAxisBoost_commutes_permutation (a : Parameters) (n : ℕ) (r : ℝ)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleAxisBoostME a n r (particlePermutation n σ x) =
      particlePermutation n σ (particleAxisBoostME a n r x) := by
  funext i
  change axisBoostMomentum a r (particlePermutation n σ x i) =
    particlePermutation n σ (fun j => axisBoostMomentum a r (x j)) i
  rw [particlePermutation_apply, particlePermutation_apply]

theorem particleAxisBoost_preserves_bosonic (a : Parameters) (n : ℕ) (r : ℝ)
    (f : bosonicHilbertSector a n) : particleAxisBoostUnitary a n r f.val ∈ bosonicHilbertSector a n := by
  apply (bosonicHilbertSector_mem a n _).mpr
  intro σ
  have h := lp_comp_commute (particleMeasure a n) (particleAxisBoostME a n (-r))
    (particlePermutation n σ) (particleAxisBoost_preserves_measure a n (-r))
    (particlePermutation_preserves_measure a n σ)
    (particleAxisBoost_commutes_permutation a n (-r) σ) f.val
  change particleAxisBoostUnitary a n r (permutationUnitary a n σ f.val) =
    permutationUnitary a n σ (particleAxisBoostUnitary a n r f.val) at h
  rw [(bosonicHilbertSector_mem a n _).mp f.property σ] at h
  exact h.symm

def bosonicAxisBoostUnitary (a : Parameters) (n : ℕ) (r : ℝ) :
    bosonicHilbertSector a n ≃ₗᵢ[ℂ] bosonicHilbertSector a n where
  toFun f := ⟨particleAxisBoostUnitary a n r f.val, particleAxisBoost_preserves_bosonic a n r f⟩
  invFun f := ⟨(particleAxisBoostUnitary a n r).symm f.val, by
    rw [particleAxisBoostUnitary_symm]
    exact particleAxisBoost_preserves_bosonic a n (-r) f⟩
  left_inv f := Subtype.ext ((particleAxisBoostUnitary a n r).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((particleAxisBoostUnitary a n r).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((particleAxisBoostUnitary a n r).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((particleAxisBoostUnitary a n r).map_smul c f.val)
  norm_map' f := (particleAxisBoostUnitary a n r).norm_map f.val

theorem bosonicAxisBoost_inverse (a : Parameters) (n : ℕ) (r : ℝ) (f : bosonicHilbertSector a n) :
    bosonicAxisBoostUnitary a n (-r) (bosonicAxisBoostUnitary a n r f) = f := by
  apply Subtype.ext
  change particleAxisBoostUnitary a n (-r) (particleAxisBoostUnitary a n r f.val) = f.val
  rw [← particleAxisBoostUnitary_symm, LinearIsometryEquiv.symm_apply_apply]

def fockAxisBoostCLM (a : Parameters) (r : ℝ) : FockHilbert a →L[ℂ] FockHilbert a :=
  HilbertSum.diagonal
    (fun n => (bosonicAxisBoostUnitary a n r).toLinearIsometry.toContinuousLinearMap)
    (fun n f => ((bosonicAxisBoostUnitary a n r).norm_map f).le)

theorem fockAxisBoost_inverse (a : Parameters) (r : ℝ) (f : FockHilbert a) :
    fockAxisBoostCLM a (-r) (fockAxisBoostCLM a r f) = f := by
  apply lp.ext
  funext n
  exact bosonicAxisBoost_inverse a n r (f n)

theorem fockAxisBoost_norm (a : Parameters) (r : ℝ) (f : FockHilbert a) :
    ‖fockAxisBoostCLM a r f‖ = ‖f‖ := by
  have hc (s : ℝ) (g : FockHilbert a) : ‖fockAxisBoostCLM a s g‖ ≤ ‖g‖ :=
    HilbertSum.diagonalLinear_norm_le
      (fun n => (bosonicAxisBoostUnitary a n s).toLinearIsometry.toContinuousLinearMap)
      (fun n f => ((bosonicAxisBoostUnitary a n s).norm_map f).le) g
  apply le_antisymm (hc r f)
  have h := hc (-r) (fockAxisBoostCLM a r f)
  rwa [fockAxisBoost_inverse] at h

def fockAxisBoostUnitary (a : Parameters) (r : ℝ) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a where
  toFun := fockAxisBoostCLM a r
  invFun := fockAxisBoostCLM a (-r)
  left_inv := fockAxisBoost_inverse a r
  right_inv f := by simpa only [neg_neg] using fockAxisBoost_inverse a (-r) f
  map_add' := (fockAxisBoostCLM a r).map_add
  map_smul' := (fockAxisBoostCLM a r).map_smul
  norm_map' := fockAxisBoost_norm a r

end AASCKleinGordon
