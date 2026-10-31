import KGOriginalWickBilocalAttachment

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem originalWickBilocalCore_smearing_eq_originalPairForm (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (h k : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x * ∫ y,k y * originalWickBilocalCore a s u v x y) =
      originalPairForm a s h k u v := by
  let N := wickJointCoreCutoff u v
  have hu : ∀ n,N≤n → u n=0 := by
    intro n hn
    exact wickCoreCutoff_zero u n ((le_max_left _ _).trans hn)
  have hv : ∀ n,N≤n → v n=0 := by
    intro n hn
    exact wickCoreCutoff_zero v n ((le_max_right _ _).trans hn)
  have hm (f g : 𝓢(Momentum,ℂ)) :
      inner ℂ (finiteParticleCoreToFock a (annihilationCore a f u))
        (finiteParticleCoreToFock a (annihilationCore a g v)) =
      ∑ n ∈ Finset.range N, inner ℂ
        (bosonicCoreToSector a n (annihilationSectorCLM a n f (u (n+1))))
        (bosonicCoreToSector a n (annihilationSectorCLM a n g (v (n+1)))) := by
    have hAu : ∀ n,N≤n → annihilationCore a f u n=0 := by
      intro n hn
      rw [wick_original_annihilation_component, hu (n+1) (by omega), map_zero]
    rw [wick_original_fock_inner_range a _ _ N hAu]
    simp only [wick_original_annihilation_component]
  have hcc : inner ℂ
      (finiteParticleCoreToFock a (annihilationCore a (spacetimeSmearingCLM a k)
        (annihilationCore a (spacetimeSmearingCLM a h) u))) (finiteParticleCoreToFock a v) =
      ∑ n ∈ Finset.range N, wickCoreChannelOriginalSectorPair a n u v h k 0 := by
    have hc := congrArg (starRingEnd ℂ)
      (wick_original_fock_inner_range a v
        (annihilationCore a (spacetimeSmearingCLM a k)
          (annihilationCore a (spacetimeSmearingCLM a h) u)) N hv)
    simpa only [map_sum, wick_original_annihilation_component,
      wickCoreChannelOriginalSectorPair, Matrix.cons_val_zero, RCLike.star_def,
      inner_conj_symm] using hc
  have hca : inner ℂ (finiteParticleCoreToFock a
      (annihilationCore a (spacetimeSmearingCLM a h) u))
      (finiteParticleCoreToFock a
        (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v)) =
      ∑ n ∈ Finset.range N, wickCoreChannelOriginalSectorPair a n u v h k 1 :=
    hm (spacetimeSmearingCLM a h) (spacetimeSmearingCLM a (conjugateSchwartzCLM k))
  have hca' : inner ℂ (finiteParticleCoreToFock a
      (annihilationCore a (spacetimeSmearingCLM a k) u))
      (finiteParticleCoreToFock a
        (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) v)) =
      ∑ n ∈ Finset.range N, wickCoreChannelOriginalSectorPair a n u v h k 2 :=
    hm (spacetimeSmearingCLM a k) (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
  have haa : inner ℂ (finiteParticleCoreToFock a u)
      (finiteParticleCoreToFock a
        (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
          (annihilationCore a (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v))) =
      ∑ n ∈ Finset.range N, wickCoreChannelOriginalSectorPair a n u v h k 3 := by
    rw [wick_original_fock_inner_range a u _ N hu]
    simp only [wick_original_annihilation_component]
    rfl
  rw [originalWickBilocalCore_test_finite_expansion]
  simp_rw [← wickCoreChannelMatrix_product_test_pairing, wickCoreChannel_smearing_eq_original]
  rw [originalPairForm_contraction_channels, hcc, hca, hca', haa]
  have hprod : (∑ j ∈ (Finset.range (wickJointCoreCutoff u v)).product
      (Finset.univ : Finset (Fin 4)), wickCoreChannelOriginalSectorPair a j.1 u v h k j.2) =
      ∑ n ∈ Finset.range N, ∑ i : Fin 4, wickCoreChannelOriginalSectorPair a n u v h k i := by
    exact Finset.sum_product _ _ _
  rw [hprod]
  have hs (n : ℕ) : (∑ i : Fin 4, wickCoreChannelOriginalSectorPair a n u v h k i) =
      wickCoreChannelOriginalSectorPair a n u v h k 0 +
      wickCoreChannelOriginalSectorPair a n u v h k 1 +
      wickCoreChannelOriginalSectorPair a n u v h k 2 +
      wickCoreChannelOriginalSectorPair a n u v h k 3 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change wickCoreChannelOriginalSectorPair a n u v h k 0 +
      (wickCoreChannelOriginalSectorPair a n u v h k 1 +
      (wickCoreChannelOriginalSectorPair a n u v h k 2 +
       wickCoreChannelOriginalSectorPair a n u v h k 3)) = _
    ring
  simp_rw [hs, Finset.sum_add_distrib]

end AASCKleinGordon
