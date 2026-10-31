import KGL2ProductMultilinear
import ComplexMultilinearPolarization
import KGCoherentSectorSeparation

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter
open scoped SchwartzMap
namespace AASCKleinGordon

theorem particleL2Product_permutation (a : Parameters) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : Fin n → OneParticleHilbert a) :
    particleL2Product a n (fun i => f (σ i))=permutationUnitary a n σ (particleL2Product a n f) := by
  apply Lp.ext
  have h1:=Lp.coeFn_compMeasurePreserving (particleL2Product a n f)
    (particlePermutation_preserves_measure a n σ)
  have h2:=(particlePermutation_preserves_measure a n σ).quasiMeasurePreserving.ae
    (particleL2Product_ae a n f)
  filter_upwards [particleL2Product_ae a n (fun i => f (σ i)),h1,h2] with x hx hy hz
  change (permutationUnitary a n σ (particleL2Product a n f) : ParticleConfiguration n → ℂ) x=
    (particleL2Product a n f : ParticleConfiguration n → ℂ) (particlePermutation n σ x) at hy
  rw [hx,hy,hz]
  unfold particleProductFunction
  simp only [particlePermutation_apply]
  have h:=Equiv.prod_comp σ (fun j => f j (x (σ.symm j)))
  simpa only [σ.symm_apply_apply] using h

def bosonicProductPairing (a : Parameters) (n : ℕ) (v : bosonicHilbertSector a n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => OneParticleHilbert a) ℂ :=
  (innerSL ℂ v.val).compContinuousMultilinearMap (particleL2ProductCMLM a n)

@[simp] theorem bosonicProductPairing_apply (a : Parameters) (n : ℕ)
    (v : bosonicHilbertSector a n) (f : Fin n → OneParticleHilbert a) :
    bosonicProductPairing a n v f=inner ℂ v.val (particleL2Product a n f) := rfl

theorem bosonicProductPairing_symmetric (a : Parameters) (n : ℕ)
    (v : bosonicHilbertSector a n) (σ : Equiv.Perm (Fin n)) (f : Fin n → OneParticleHilbert a) :
    bosonicProductPairing a n v (fun i => f (σ i))=bosonicProductPairing a n v f := by
  simp only [bosonicProductPairing_apply,particleL2Product_permutation]
  have h:=(permutationUnitary a n σ).inner_map_map v.val (particleL2Product a n f)
  rw [(bosonicHilbertSector_mem a n _).mp v.property σ] at h
  exact h

theorem bosonic_schwartz_diagonal_orthogonality_forces_all_products
    (a : Parameters) (n : ℕ) (v : bosonicHilbertSector a n)
    (diagonal : ∀ f : 𝓢(Momentum,ℂ),inner ℂ v (bosonicTensorPowerHilbert a f n)=0) :
    ∀ f : Fin n → OneParticleHilbert a,inner ℂ v.val (particleL2Product a n f)=0 := by
  have hd : ∀ u : OneParticleHilbert a,bosonicProductPairing a n v (fun _ => u)=0 := by
    have hc : Continuous (fun u : OneParticleHilbert a => bosonicProductPairing a n v (fun _ => u)) :=
      (bosonicProductPairing a n v).cont.comp (continuous_pi (fun _ => continuous_id))
    have he : (fun u : OneParticleHilbert a => bosonicProductPairing a n v (fun _ => u))=
        (fun _ => (0 : ℂ)) := by
      apply hc.ext_on (oneParticleSchwartz_dense a) continuous_const
      rintro _ ⟨f,rfl⟩
      change bosonicProductPairing a n v (fun _ => oneParticleSchwartzToHilbert a f)=0
      rw [bosonicProductPairing_apply,particleL2Product_schwartz_diagonal]
      exact diagonal f
    exact fun u => congrFun he u
  exact symmetric_complex_multilinear_diagonal_zero n (bosonicProductPairing a n v)
    (bosonicProductPairing_symmetric a n v) hd

theorem exponentialVector_orthogonal_forces_sector_product_orthogonality
    (a : Parameters) (v : FockHilbert a)
    (h : ∀ f : 𝓢(Momentum,ℂ),inner ℂ v (exponentialVector a f)=0) :
    ∀ (n : ℕ) (f : Fin n → OneParticleHilbert a),inner ℂ (v n).val (particleL2Product a n f)=0 := by
  intro n
  exact bosonic_schwartz_diagonal_orthogonality_forces_all_products a n (v n)
    (fun f => exponentialVector_orthogonal_separates_sectors a v h f n)

end AASCKleinGordon
