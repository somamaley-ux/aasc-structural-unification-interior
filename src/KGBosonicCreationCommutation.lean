import KGCoreFieldOperations

noncomputable section
open scoped SchwartzMap DirectSum
namespace AASCKleinGordon

theorem schwartzSymmetrizer_permutation (n : ℕ) (τ : Equiv.Perm (Fin n))
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    schwartzSymmetrizer n (schwartzPermutation n τ H) = schwartzSymmetrizer n H := by
  ext x
  simp only [schwartzSymmetrizer_apply, schwartzPermutation_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ)
    (fun σ : Equiv.Perm (Fin n) => H (fun i => x (σ i)))

theorem tensorInsert_permutation (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (σ : Equiv.Perm (Fin n)) (H : 𝓢(ParticleConfiguration n,ℂ)) :
    particleTensorInsertCLM n f (schwartzPermutation n σ H) =
      schwartzPermutation (n+1) (liftParticlePermutation σ) (particleTensorInsertCLM n f H) := by
  ext x
  simp only [particleTensorInsertCLM_apply, schwartzPermutation_apply, liftParticlePermutation_zero]
  congr 1

theorem symmetrizer_tensorInsert_symmetrizer (n : ℕ) (f : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    schwartzSymmetrizer (n+1) (particleTensorInsertCLM n f (schwartzSymmetrizer n H)) =
      schwartzSymmetrizer (n+1) (particleTensorInsertCLM n f H) := by
  have hs : schwartzSymmetrizer n H = permutationAverageCoefficient n •
      ∑ σ : Equiv.Perm (Fin n), schwartzPermutation n σ H := by
    simp only [schwartzSymmetrizer, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  rw [hs, map_smul, map_sum, map_smul, map_sum]
  simp_rw [tensorInsert_permutation, schwartzSymmetrizer_permutation]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [permutationAverageCoefficient, hc]

theorem double_tensorInsert_swap (n : ℕ) (f g : 𝓢(Momentum,ℂ))
    (H : 𝓢(ParticleConfiguration n,ℂ)) :
    particleTensorInsertCLM (n+1) f (particleTensorInsertCLM n g H) =
      schwartzPermutation (n+2) (Equiv.swap 0 1)
        (particleTensorInsertCLM (n+1) g (particleTensorInsertCLM n f H)) := by
  ext x
  simp only [particleTensorInsertCLM_apply, schwartzPermutation_apply]
  simp only [Equiv.swap_apply_left]
  have ht : Fin.tail (Fin.tail (fun i => x (Equiv.swap 0 1 i))) = Fin.tail (Fin.tail x) := by
    funext i
    have hi0 : i.succ.succ ≠ (0 : Fin (n+2)) := by simp
    have hi1 : i.succ.succ ≠ (1 : Fin (n+2)) := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_succ, Fin.val_one] at hv
      omega
    simp [Fin.tail, Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  rw [ht]
  have htail0 : Fin.tail (fun i => x (Equiv.swap 0 1 i)) 0 = x 0 := by
    change x (Equiv.swap 0 1 1) = x 0
    rw [Equiv.swap_apply_right]
  rw [htail0]
  change f (x 0) * (g (x 1) * H (Fin.tail (Fin.tail x))) = _
  ring

theorem creationSectors_commute (n : ℕ) (f g : 𝓢(Momentum,ℂ)) (H : bosonicSchwartz n) :
    creationSectorCLM (n+1) f (creationSectorCLM n g H) =
      creationSectorCLM (n+1) g (creationSectorCLM n f H) := by
  apply Subtype.ext
  simp only [creationSectorCLM_apply, map_smul, smul_smul]
  rw [symmetrizer_tensorInsert_symmetrizer, symmetrizer_tensorInsert_symmetrizer]
  rw [double_tensorInsert_swap, schwartzSymmetrizer_permutation]

theorem creationCore_commute (f g : 𝓢(Momentum,ℂ)) :
    (creationCore f).comp (creationCore g) = (creationCore g).comp (creationCore f) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro H
  simp only [LinearMap.comp_apply, creationCore_lof]
  rw [creationSectors_commute]

end AASCKleinGordon
