import L2RealMultiplicationCoefficients
import KGBosonicCoreEmbedding
import KGCoreSpatialMomentum

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon

theorem bosonic_multiplication_output_fixed (a : Parameters) (n : ℕ)
    (c : ParticleConfiguration n → ℂ)
    (hc : ∀ (σ : Equiv.Perm (Fin n)) x,c (particlePermutation n σ x)=c x)
    (f : bosonicHilbertSector a n) (g : ParticleHilbert a n)
    (hg : g=ᵐ[particleMeasure a n] (fun x => c x*f.val x)) :
    g ∈ bosonicHilbertSector a n := by
  apply (bosonicHilbertSector_mem a n g).2
  intro σ
  apply Lp.ext
  have hp := particlePermutation_preserves_measure a n σ
  have h1 := Lp.coeFn_compMeasurePreserving g hp
  have h2 := hp.quasiMeasurePreserving.ae hg
  have h3 := Lp.coeFn_compMeasurePreserving f.val hp
  have hf := (bosonicHilbertSector_mem a n f.val).1 f.property σ
  filter_upwards [h1,h2,h3,hg] with x hx hy hz hw
  simp only [Function.comp_apply] at hx hz
  change (Lp.compMeasurePreserving (particlePermutation n σ) hp g) x=g x
  rw [hx,hy,hw,hc σ x]
  apply congrArg (fun z : ℂ => c x*z)
  calc
    f.val (particlePermutation n σ x)=
        (Lp.compMeasurePreserving (particlePermutation n σ) hp f.val) x := hz.symm
    _ = f.val x := congrArg (fun z : ParticleHilbert a n => z x) hf

theorem particleGraphBoundedA_preserves_bosonic (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (f : bosonicHilbertSector a n) :
    Multiplication.graphBoundedA v hv f.val ∈ bosonicHilbertSector a n :=
  bosonic_multiplication_output_fixed a n _
    (fun σ x => congrArg Multiplication.graphCoefficientA (hi σ x)) f _
    (Multiplication.graphBoundedA_ae v hv f.val)

theorem particleGraphBoundedB_preserves_bosonic (a : Parameters) (n : ℕ)
    (v : ParticleConfiguration n → ℝ) (hv : Measurable v)
    (hi : ∀ (σ : Equiv.Perm (Fin n)) x,v (particlePermutation n σ x)=v x)
    (f : bosonicHilbertSector a n) :
    Multiplication.graphBoundedB v hv f.val ∈ bosonicHilbertSector a n :=
  bosonic_multiplication_output_fixed a n _
    (fun σ x => congrArg Multiplication.graphCoefficientB (hi σ x)) f _
    (Multiplication.graphBoundedB_ae v hv f.val)

theorem totalMomentum_particlePermutation (n : ℕ) (j : Fin 3)
    (σ : Equiv.Perm (Fin n)) (x : ParticleConfiguration n) :
    totalMomentumCLM n j (particlePermutation n σ x)=totalMomentumCLM n j x := by
  have he : particlePermutation n σ x=(fun i => x (σ.symm i)) :=
    funext (particlePermutation_apply n σ x)
  rw [he]
  exact totalMomentum_permutation n j σ.symm x

end AASCKleinGordon
