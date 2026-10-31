import KGGeneralLorentzOneParticleUnitary
import KGGeneralLorentzOriginalCore
import KGFockBoundedMultipliers

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
namespace AASCKleinGordon

def particleLorentzME (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    ParticleConfiguration n ≃ᵐ ParticleConfiguration n where
  toEquiv :=
    { toFun := fun x i => lorentzShellMap a L (x i)
      invFun := fun x i => lorentzShellMap a (L⁻¹) (x i)
      left_inv := fun x => funext (fun i => lorentzShellMap_inverse_left a L (x i))
      right_inv := fun x => funext (fun i => by
        simpa only [inv_inv] using lorentzShellMap_inverse_left a (L⁻¹) (x i)) }
  measurable_toFun := measurable_pi_iff.mpr (fun i =>
    (lorentzMomentumME a L).measurable.comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.mpr (fun i =>
    (lorentzMomentumME a (L⁻¹)).measurable.comp (measurable_pi_apply i))

theorem particleLorentz_preserves_measure (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    MeasurePreserving (particleLorentzME a n L) (particleMeasure a n) (particleMeasure a n) :=
  measurePreserving_pi (fun _ : Fin n => wignerMeasure a) (fun _ => wignerMeasure a)
    (fun _ => lorentzShellMap_preserves_wignerMeasure a L)

def particleLorentzUnitary (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    ParticleHilbert a n ≃ₗᵢ[ℂ] ParticleHilbert a n :=
  lpMeasureEquivalence (particleLorentzME a n (L⁻¹))
    (particleLorentz_preserves_measure a n (L⁻¹))
    (MeasurePreserving.symm (particleLorentzME a n (L⁻¹))
      (particleLorentz_preserves_measure a n (L⁻¹)))

theorem particleLorentzUnitary_ae (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) (f : ParticleHilbert a n) :
    (particleLorentzUnitary a n L f : ParticleConfiguration n → ℂ) =ᵐ[particleMeasure a n]
      (fun x => f (fun i => lorentzShellMap a (L⁻¹) (x i))) :=
  Lp.coeFn_compMeasurePreserving f (particleLorentz_preserves_measure a n (L⁻¹))

theorem particleLorentzUnitary_symm (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (f : ParticleHilbert a n) :
    (particleLorentzUnitary a n L).symm f = particleLorentzUnitary a n (L⁻¹) f := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving f
    (MeasurePreserving.symm (particleLorentzME a n (L⁻¹))
      (particleLorentz_preserves_measure a n (L⁻¹)))
  have h2 := particleLorentzUnitary_ae a n (L⁻¹) f
  filter_upwards [h1,h2] with x hx hy
  exact hx.trans hy.symm

theorem particleLorentz_commutes_permutation (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    particleLorentzME a n L (particlePermutation n σ x) =
      particlePermutation n σ (particleLorentzME a n L x) := by
  funext i
  change lorentzShellMap a L (particlePermutation n σ x i) =
    particlePermutation n σ (fun j => lorentzShellMap a L (x j)) i
  rw [particlePermutation_apply, particlePermutation_apply]

theorem particleLorentz_preserves_bosonic (a : Parameters) (n : ℕ) (L : ProperLorentzTransform)
    (f : bosonicHilbertSector a n) : particleLorentzUnitary a n L f.val ∈ bosonicHilbertSector a n := by
  apply (bosonicHilbertSector_mem a n _).mpr
  intro σ
  have h := lp_comp_commute (particleMeasure a n) (particleLorentzME a n (L⁻¹))
    (particlePermutation n σ) (particleLorentz_preserves_measure a n (L⁻¹))
    (particlePermutation_preserves_measure a n σ)
    (particleLorentz_commutes_permutation a n (L⁻¹) σ) f.val
  change particleLorentzUnitary a n L (permutationUnitary a n σ f.val) =
    permutationUnitary a n σ (particleLorentzUnitary a n L f.val) at h
  rw [(bosonicHilbertSector_mem a n _).mp f.property σ] at h
  exact h.symm

def bosonicLorentzUnitary (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) :
    bosonicHilbertSector a n ≃ₗᵢ[ℂ] bosonicHilbertSector a n where
  toFun f := ⟨particleLorentzUnitary a n L f.val, particleLorentz_preserves_bosonic a n L f⟩
  invFun f := ⟨(particleLorentzUnitary a n L).symm f.val, by
    rw [particleLorentzUnitary_symm]
    exact particleLorentz_preserves_bosonic a n (L⁻¹) f⟩
  left_inv f := Subtype.ext ((particleLorentzUnitary a n L).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((particleLorentzUnitary a n L).apply_symm_apply f.val)
  map_add' f g := Subtype.ext ((particleLorentzUnitary a n L).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((particleLorentzUnitary a n L).map_smul c f.val)
  norm_map' f := (particleLorentzUnitary a n L).norm_map f.val

theorem bosonicLorentz_inverse (a : Parameters) (n : ℕ) (L : ProperLorentzTransform) (f : bosonicHilbertSector a n) :
    bosonicLorentzUnitary a n (L⁻¹) (bosonicLorentzUnitary a n L f) = f := by
  apply Subtype.ext
  change particleLorentzUnitary a n (L⁻¹) (particleLorentzUnitary a n L f.val) = f.val
  rw [← particleLorentzUnitary_symm, LinearIsometryEquiv.symm_apply_apply]

def fockLorentzCLM (a : Parameters) (L : ProperLorentzTransform) : FockHilbert a →L[ℂ] FockHilbert a :=
  HilbertSum.diagonal
    (fun n => (bosonicLorentzUnitary a n L).toLinearIsometry.toContinuousLinearMap)
    (fun n f => ((bosonicLorentzUnitary a n L).norm_map f).le)

theorem fockLorentz_inverse (a : Parameters) (L : ProperLorentzTransform) (f : FockHilbert a) :
    fockLorentzCLM a (L⁻¹) (fockLorentzCLM a L f) = f := by
  apply lp.ext
  funext n
  exact bosonicLorentz_inverse a n L (f n)

theorem fockLorentz_norm (a : Parameters) (L : ProperLorentzTransform) (f : FockHilbert a) :
    ‖fockLorentzCLM a L f‖ = ‖f‖ := by
  have hc (s : ProperLorentzTransform) (g : FockHilbert a) : ‖fockLorentzCLM a s g‖ ≤ ‖g‖ :=
    HilbertSum.diagonalLinear_norm_le
      (fun n => (bosonicLorentzUnitary a n s).toLinearIsometry.toContinuousLinearMap)
      (fun n f => ((bosonicLorentzUnitary a n s).norm_map f).le) g
  apply le_antisymm (hc L f)
  have h := hc (L⁻¹) (fockLorentzCLM a L f)
  rwa [fockLorentz_inverse] at h

def fockLorentzUnitary (a : Parameters) (L : ProperLorentzTransform) : FockHilbert a ≃ₗᵢ[ℂ] FockHilbert a where
  toFun := fockLorentzCLM a L
  invFun := fockLorentzCLM a (L⁻¹)
  left_inv := fockLorentz_inverse a L
  right_inv f := by simpa only [inv_inv] using fockLorentz_inverse a (L⁻¹) f
  map_add' := (fockLorentzCLM a L).map_add
  map_smul' := (fockLorentzCLM a L).map_smul
  norm_map' := fockLorentz_norm a L

end AASCKleinGordon
