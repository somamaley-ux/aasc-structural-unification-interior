import KGWickStateKernelLaws
import KGWickCoreCutoffIndependence
import KGOriginalLocalWickSquare

noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wickCoreChannelMatrix_add_left (a : Parameters) (n : ℕ)
    (u u' v : FiniteParticleCore) (i : Fin 4) (x y : Spacetime) :
    wickCoreChannelMatrix a n (u+u') v i x y =
      wickCoreChannelMatrix a n u v i x y + wickCoreChannelMatrix a n u' v i x y := by
  unfold wickCoreChannelMatrix
  rw [wickCoreChannelStateKernel_add_left]
  exact wickBilocalMatrix_add_kernel a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ _ x y

theorem wickCoreChannelMatrix_add_right (a : Parameters) (n : ℕ)
    (u v v' : FiniteParticleCore) (i : Fin 4) (x y : Spacetime) :
    wickCoreChannelMatrix a n u (v+v') i x y =
      wickCoreChannelMatrix a n u v i x y + wickCoreChannelMatrix a n u v' i x y := by
  unfold wickCoreChannelMatrix
  rw [wickCoreChannelStateKernel_add_right]
  exact wickBilocalMatrix_add_kernel a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ _ x y

theorem wickCoreChannelMatrix_smul_left (a : Parameters) (n : ℕ) (c : ℂ)
    (u v : FiniteParticleCore) (i : Fin 4) (x y : Spacetime) :
    wickCoreChannelMatrix a n (c • u) v i x y = star c * wickCoreChannelMatrix a n u v i x y := by
  unfold wickCoreChannelMatrix
  rw [wickCoreChannelStateKernel_smul_left]
  exact wickBilocalMatrix_smul_kernel a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ _ x y

theorem wickCoreChannelMatrix_smul_right (a : Parameters) (n : ℕ) (c : ℂ)
    (u v : FiniteParticleCore) (i : Fin 4) (x y : Spacetime) :
    wickCoreChannelMatrix a n u (c • v) i x y = c * wickCoreChannelMatrix a n u v i x y := by
  unfold wickCoreChannelMatrix
  rw [wickCoreChannelStateKernel_smul_right]
  exact wickBilocalMatrix_smul_kernel a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n i) (wickCoreChannelFrequency1_temperate a n i) _ _ x y

def WickCoreTailBound (u : FiniteParticleCore) (N : ℕ) : Prop := ∀ n, N≤n → u n=0

theorem wickCoreTailBound_cutoff (u : FiniteParticleCore) : WickCoreTailBound u (wickCoreCutoff u) :=
  wickCoreCutoff_zero u

theorem WickCoreTailBound.mono {u : FiniteParticleCore} {N M : ℕ}
    (h : WickCoreTailBound u N) (hNM : N≤M) : WickCoreTailBound u M :=
  fun n hn => h n (hNM.trans hn)

theorem WickCoreTailBound.add {u v : FiniteParticleCore} {N : ℕ}
    (hu : WickCoreTailBound u N) (hv : WickCoreTailBound v N) : WickCoreTailBound (u+v) N := by
  intro n hn
  simp only [DirectSum.add_apply, hu n hn, hv n hn, add_zero]

theorem WickCoreTailBound.smul {u : FiniteParticleCore} {N : ℕ}
    (hu : WickCoreTailBound u N) (c : ℂ) : WickCoreTailBound (c • u) N := by
  intro n hn
  simp only [DirectSum.smul_apply, hu n hn, smul_zero]

theorem originalWickBilocalCoreAt_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (N : ℕ) (x y : Spacetime) :
    originalWickBilocalCoreAt a s (u+u') v N x y =
      originalWickBilocalCoreAt a s u v N x y + originalWickBilocalCoreAt a s u' v N x y := by
  unfold originalWickBilocalCoreAt
  simp_rw [wickCoreChannelMatrix_add_left, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem originalWickBilocalCoreAt_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (N : ℕ) (x y : Spacetime) :
    originalWickBilocalCoreAt a s u (v+v') N x y =
      originalWickBilocalCoreAt a s u v N x y + originalWickBilocalCoreAt a s u v' N x y := by
  unfold originalWickBilocalCoreAt
  simp_rw [wickCoreChannelMatrix_add_right, mul_add]
  rw [Finset.sum_add_distrib, mul_add]

theorem originalWickBilocalCoreAt_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (N : ℕ) (x y : Spacetime) :
    originalWickBilocalCoreAt a s (c • u) v N x y =
      star c * originalWickBilocalCoreAt a s u v N x y := by
  unfold originalWickBilocalCoreAt
  simp_rw [wickCoreChannelMatrix_smul_left, mul_left_comm (wickCoreChannelCoefficient _ _) (star c)]
  rw [← Finset.mul_sum]
  ring

theorem originalWickBilocalCoreAt_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (N : ℕ) (x y : Spacetime) :
    originalWickBilocalCoreAt a s u (c • v) N x y =
      c * originalWickBilocalCoreAt a s u v N x y := by
  unfold originalWickBilocalCoreAt
  simp_rw [wickCoreChannelMatrix_smul_right, mul_left_comm (wickCoreChannelCoefficient _ _) c]
  rw [← Finset.mul_sum]
  ring

theorem originalWickBilocalCore_add_left (a : Parameters) (s : ℝ)
    (u u' v : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s (u+u') v x y =
      originalWickBilocalCore a s u v x y + originalWickBilocalCore a s u' v x y := by
  let N := max (wickCoreCutoff u) (max (wickCoreCutoff u') (wickCoreCutoff v))
  have hu : WickCoreTailBound u N := (wickCoreTailBound_cutoff u).mono (by dsimp [N]; omega)
  have hu' : WickCoreTailBound u' N := (wickCoreTailBound_cutoff u').mono (by dsimp [N]; omega)
  have hv : WickCoreTailBound v N := (wickCoreTailBound_cutoff v).mono (by dsimp [N]; omega)
  rw [originalWickBilocalCore_eq_any_cutoff a s (u+u') v N (hu.add hu') hv,
    originalWickBilocalCore_eq_any_cutoff a s u v N hu hv,
    originalWickBilocalCore_eq_any_cutoff a s u' v N hu' hv]
  exact originalWickBilocalCoreAt_add_left a s u u' v N x y

theorem originalWickBilocalCore_add_right (a : Parameters) (s : ℝ)
    (u v v' : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s u (v+v') x y =
      originalWickBilocalCore a s u v x y + originalWickBilocalCore a s u v' x y := by
  let N := max (wickCoreCutoff u) (max (wickCoreCutoff v) (wickCoreCutoff v'))
  have hu : WickCoreTailBound u N := (wickCoreTailBound_cutoff u).mono (by dsimp [N]; omega)
  have hv : WickCoreTailBound v N := (wickCoreTailBound_cutoff v).mono (by dsimp [N]; omega)
  have hv' : WickCoreTailBound v' N := (wickCoreTailBound_cutoff v').mono (by dsimp [N]; omega)
  rw [originalWickBilocalCore_eq_any_cutoff a s u (v+v') N hu (hv.add hv'),
    originalWickBilocalCore_eq_any_cutoff a s u v N hu hv,
    originalWickBilocalCore_eq_any_cutoff a s u v' N hu hv']
  exact originalWickBilocalCoreAt_add_right a s u v v' N x y

theorem originalWickBilocalCore_smul_left (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s (c • u) v x y = star c * originalWickBilocalCore a s u v x y := by
  let N := max (wickCoreCutoff u) (wickCoreCutoff v)
  have hu : WickCoreTailBound u N := (wickCoreTailBound_cutoff u).mono (le_max_left _ _)
  have hv : WickCoreTailBound v N := (wickCoreTailBound_cutoff v).mono (le_max_right _ _)
  rw [originalWickBilocalCore_eq_any_cutoff a s (c • u) v N (hu.smul c) hv,
    originalWickBilocalCore_eq_any_cutoff a s u v N hu hv]
  exact originalWickBilocalCoreAt_smul_left a s c u v N x y

theorem originalWickBilocalCore_smul_right (a : Parameters) (s : ℝ) (c : ℂ)
    (u v : FiniteParticleCore) (x y : Spacetime) :
    originalWickBilocalCore a s u (c • v) x y = c * originalWickBilocalCore a s u v x y := by
  let N := max (wickCoreCutoff u) (wickCoreCutoff v)
  have hu : WickCoreTailBound u N := (wickCoreTailBound_cutoff u).mono (le_max_left _ _)
  have hv : WickCoreTailBound v N := (wickCoreTailBound_cutoff v).mono (le_max_right _ _)
  rw [originalWickBilocalCore_eq_any_cutoff a s u (c • v) N hu (hv.smul c),
    originalWickBilocalCore_eq_any_cutoff a s u v N hu hv]
  exact originalWickBilocalCoreAt_smul_right a s c u v N x y

end AASCKleinGordon
