import KGBosonicCoreEmbedding

noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def schwartzPermutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => Momentum) σ.symm)

theorem schwartzPermutation_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    schwartzPermutation n σ f x=f (fun i => x (σ i)) := by
  change f (particlePermutation n σ.symm x)=_
  have he : particlePermutation n σ.symm x=(fun i => x (σ i)) := by
    ext i
    simp only [particlePermutation_apply,Equiv.symm_symm]
  rw [he]

def permutationAverageCoefficient (n : ℕ) : ℂ := (Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹

def schwartzSymmetrizer (n : ℕ) : 𝓢(ParticleConfiguration n,ℂ) →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  permutationAverageCoefficient n • ∑ σ : Equiv.Perm (Fin n),schwartzPermutation n σ

theorem schwartzSymmetrizer_apply (n : ℕ) (f : 𝓢(ParticleConfiguration n,ℂ)) (x : ParticleConfiguration n) :
    schwartzSymmetrizer n f x=permutationAverageCoefficient n*
      ∑ σ : Equiv.Perm (Fin n),f (fun i => x (σ i)) := by
  simp [schwartzSymmetrizer,schwartzPermutation_apply]

theorem schwartzSymmetrizer_bosonic (n : ℕ) (f : 𝓢(ParticleConfiguration n,ℂ)) :
    schwartzSymmetrizer n f ∈ bosonicSchwartz n := by
  intro τ x
  simp only [schwartzSymmetrizer_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin n) => f (fun i => x (σ i)))

theorem schwartzPermutation_intertwines (a : Parameters) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : 𝓢(ParticleConfiguration n,ℂ)) :
    particleSchwartzToHilbert a n (schwartzPermutation n σ f)=
      permutationUnitary a n σ.symm (particleSchwartzToHilbert a n f) := by
  apply Lp.ext
  have h₁ := (schwartzPermutation n σ f).coeFn_toLp 2 (particleMeasure a n)
  have h₂ := Lp.coeFn_compMeasurePreserving (particleSchwartzToHilbert a n f)
    (particlePermutation_preserves_measure a n σ.symm)
  have h₃ := (particlePermutation_preserves_measure a n σ.symm).quasiMeasurePreserving.ae
    (f.coeFn_toLp 2 (particleMeasure a n))
  filter_upwards [h₁,h₂,h₃] with x hx hy hz
  have he : schwartzPermutation n σ f x=f (particlePermutation n σ.symm x) := rfl
  exact hx.trans (he.trans (hy.trans hz).symm)

def hilbertSymmetrizer (a : Parameters) (n : ℕ) : ParticleHilbert a n →L[ℂ] ParticleHilbert a n :=
  permutationAverageCoefficient n • ∑ σ : Equiv.Perm (Fin n),
    (permutationUnitary a n σ.symm).toLinearIsometry.toContinuousLinearMap

theorem symmetrizer_intertwines (a : Parameters) (n : ℕ) (f : 𝓢(ParticleConfiguration n,ℂ)) :
    particleSchwartzToHilbert a n (schwartzSymmetrizer n f)=
      hilbertSymmetrizer a n (particleSchwartzToHilbert a n f) := by
  simp only [schwartzSymmetrizer,hilbertSymmetrizer,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_smul,map_sum]
  congr 1

end AASCKleinGordon
