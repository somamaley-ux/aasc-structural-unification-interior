import KGParticleAdjointness
import KGBosonicCoreDensity

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon

theorem hilbertSymmetrizer_inner_bosonic (a : Parameters) (n : ℕ)
    (H : ParticleHilbert a n) (K : bosonicHilbertSector a n) :
    inner ℂ (hilbertSymmetrizer a n H) K.val = inner ℂ H K.val := by
  have hfix (σ : Equiv.Perm (Fin n)) : permutationUnitary a n σ.symm K.val = K.val :=
    (bosonicHilbertSector_mem a n _).mp K.property σ.symm
  have hu (σ : Equiv.Perm (Fin n)) :
      inner ℂ (permutationUnitary a n σ.symm H) K.val = inner ℂ H K.val := by
    calc
      _ = inner ℂ (permutationUnitary a n σ.symm H)
          (permutationUnitary a n σ.symm K.val) :=
        congrArg (fun z => inner ℂ (permutationUnitary a n σ.symm H) z) (hfix σ).symm
      _ = _ := (permutationUnitary a n σ.symm).inner_map_map H K.val
  simp only [hilbertSymmetrizer, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    inner_smul_left, sum_inner]
  change (starRingEnd ℂ) (permutationAverageCoefficient n) *
    (∑ σ : Equiv.Perm (Fin n), inner ℂ (permutationUnitary a n σ.symm H) K.val) = _
  simp only [hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [permutationAverageCoefficient, smul_eq_mul, hc]

theorem schwartzSymmetrizer_inner_bosonic (a : Parameters) (n : ℕ)
    (H : 𝓢(ParticleConfiguration n,ℂ)) (K : bosonicSchwartz n) :
    inner ℂ (particleSchwartzToHilbert a n (schwartzSymmetrizer n H))
      (particleSchwartzToHilbert a n K.val) =
    inner ℂ (particleSchwartzToHilbert a n H) (particleSchwartzToHilbert a n K.val) := by
  rw [symmetrizer_intertwines]
  exact hilbertSymmetrizer_inner_bosonic a n _ (bosonicCoreToSector a n K)

theorem annihilationSector_val (a : Parameters) (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (K : bosonicSchwartz (n+1)) :
    (annihilationSectorCLM a n f K).val = (Real.sqrt (n+1) : ℂ) •
      particleContractionCLM a n f K.val := rfl

theorem creation_annihilation_sector_adjoint (a : Parameters) (n : ℕ)
    (f : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) (K : bosonicSchwartz (n+1)) :
    inner ℂ (bosonicCoreToSector a (n+1) (creationSectorCLM n f H))
      (bosonicCoreToSector a (n+1) K) =
    inner ℂ (bosonicCoreToSector a n H)
      (bosonicCoreToSector a n (annihilationSectorCLM a n f K)) := by
  change inner ℂ (particleSchwartzToHilbert a (n+1) (creationSectorCLM n f H).val)
      (particleSchwartzToHilbert a (n+1) K.val) =
    inner ℂ (particleSchwartzToHilbert a n H.val)
      (particleSchwartzToHilbert a n (annihilationSectorCLM a n f K).val)
  rw [creationSectorCLM_apply, annihilationSector_val, map_smul, map_smul,
    inner_smul_left, inner_smul_right, schwartzSymmetrizer_inner_bosonic,
    particle_tensor_contraction_adjoint]
  simp

end AASCKleinGordon
