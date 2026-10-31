import KGOriginalWickBilocalCore

noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

@[simp] theorem wickAAStateKernel_zero_left (n : ℕ) (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    wickAAStateKernel n 0 v = 0 := by
  apply SchwartzMap.ext
  intro z
  simp only [wickAAStateKernel_apply, SchwartzMap.zero_apply, star_zero, zero_mul]

@[simp] theorem wickMixedStateKernel_zero_left (n : ℕ)
    (v : 𝓢(ParticleConfiguration (n+1),ℂ)) : wickMixedStateKernel n 0 v = 0 := by
  apply SchwartzMap.ext
  intro z
  simp only [wickMixedStateKernel_apply, SchwartzMap.zero_apply, star_zero, zero_mul]

theorem wickCoreChannelStateKernel_zero_tail (n N : ℕ) (u v : FiniteParticleCore)
    (hu : ∀ j,N≤j → u j=0) (hv : ∀ j,N≤j → v j=0) (hn : N≤n) (i : Fin 4) :
    wickCoreChannelStateKernel n u v i = 0 := by
  fin_cases i
  · change SchwartzOperations.conjugateSchwartzCLM (wickAAStateKernel n (v n).val (u (n+2)).val)=0
    rw [hv n hn]
    simp
  · change wickMixedStateKernel n (u (n+1)).val (v (n+1)).val=0
    rw [hu (n+1) (by omega)]
    simp
  · change wickMixedStateKernel n (u (n+1)).val (v (n+1)).val=0
    rw [hu (n+1) (by omega)]
    simp
  · change wickAAStateKernel n (u n).val (v (n+2)).val=0
    rw [hu n hn]
    simp

theorem wickCoreChannelMatrix_zero_tail (a : Parameters) (n N : ℕ) (u v : FiniteParticleCore)
    (hu : ∀ j,N≤j → u j=0) (hv : ∀ j,N≤j → v j=0) (hn : N≤n) (i : Fin 4)
    (x y : Spacetime) : wickCoreChannelMatrix a n u v i x y = 0 := by
  unfold wickCoreChannelMatrix
  rw [wickCoreChannelStateKernel_zero_tail n N u v hu hv hn i]
  simp [wickBilocalMatrix, wickPhaseStateKernel, wickLocalMatrix]

def originalWickBilocalCoreAt (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (N : ℕ) (x y : Spacetime) : ℂ :=
  (s : ℂ)^2 * ∑ j ∈ (Finset.range N).product (Finset.univ : Finset (Fin 4)),
    wickCoreChannelCoefficient j.1 j.2 * wickCoreChannelMatrix a j.1 u v j.2 x y

theorem originalWickBilocalCoreAt_extend (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (N M : ℕ) (hNM : N≤M) (hu : ∀ j,N≤j → u j=0) (hv : ∀ j,N≤j → v j=0)
    (x y : Spacetime) : originalWickBilocalCoreAt a s u v N x y =
      originalWickBilocalCoreAt a s u v M x y := by
  classical
  unfold originalWickBilocalCoreAt
  congr 1
  apply Finset.sum_subset
    (Finset.product_subset_product (Finset.range_mono hNM) (Finset.Subset.refl _))
  intro j hj hnot
  have hn : N≤j.1 := by
    simpa only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, not_lt] using hnot
  rw [wickCoreChannelMatrix_zero_tail a j.1 N u v hu hv hn]
  exact mul_zero _

theorem originalWickBilocalCore_eq_any_cutoff (a : Parameters) (s : ℝ) (u v : FiniteParticleCore)
    (N : ℕ) (hu : ∀ j,N≤j → u j=0) (hv : ∀ j,N≤j → v j=0) (x y : Spacetime) :
    originalWickBilocalCore a s u v x y = originalWickBilocalCoreAt a s u v N x y := by
  let J := wickJointCoreCutoff u v
  have hju : ∀ j,J≤j → u j=0 := by
    intro j hj
    exact wickCoreCutoff_zero u j ((le_max_left _ _).trans hj)
  have hjv : ∀ j,J≤j → v j=0 := by
    intro j hj
    exact wickCoreCutoff_zero v j ((le_max_right _ _).trans hj)
  change originalWickBilocalCoreAt a s u v J x y = _
  exact (originalWickBilocalCoreAt_extend a s u v J (max J N) (le_max_left _ _) hju hjv x y).trans
    (originalWickBilocalCoreAt_extend a s u v N (max J N) (le_max_right _ _) hu hv x y).symm

end AASCKleinGordon
