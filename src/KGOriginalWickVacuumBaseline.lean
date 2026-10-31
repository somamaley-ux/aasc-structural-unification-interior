import KGOriginalLocalWickStateLaws

noncomputable section
set_option maxHeartbeats 4000000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem vacuumCore_tail_bound_one : WickCoreTailBound vacuumCore 1 := by
  intro n hn
  have hn0 : n≠0 := by omega
  simp [vacuumCore, DirectSum.lof_eq_of, DirectSum.of_apply, hn0, Ne.symm hn0]

theorem wickCoreChannelStateKernel_vacuum_sectors (n : ℕ) (u v : FiniteParticleCore)
    (hu : WickCoreTailBound u 1) (hv : WickCoreTailBound v 1) (i : Fin 4) :
    wickCoreChannelStateKernel n u v i = 0 := by
  apply SchwartzMap.ext
  intro z
  have hu1 := hu (n+1) (by omega)
  have hu2 := hu (n+2) (by omega)
  have hv2 := hv (n+2) (by omega)
  fin_cases i <;> simp [wickCoreChannelStateKernel, wickAAStateKernel_apply, hu1, hu2, hv2]

theorem originalWickBilocalCore_vacuum_sectors (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (hu : WickCoreTailBound u 1) (hv : WickCoreTailBound v 1)
    (x y : Spacetime) : originalWickBilocalCore a s u v x y = 0 := by
  have hz (n : ℕ) (i : Fin 4) : wickCoreChannelMatrix a n u v i x y = 0 := by
    unfold wickCoreChannelMatrix
    rw [wickCoreChannelStateKernel_vacuum_sectors n u v hu hv i]
    simp [wickBilocalMatrix, wickPhaseStateKernel, wickLocalMatrix]
  simp [originalWickBilocalCore, hz]

theorem originalWickBilocalCore_vacuum (a : Parameters) (s : ℝ) (x y : Spacetime) :
    originalWickBilocalCore a s vacuumCore vacuumCore x y = 0 :=
  originalWickBilocalCore_vacuum_sectors a s _ _
    vacuumCore_tail_bound_one vacuumCore_tail_bound_one x y

theorem originalWickSquareMatrix_vacuum (a : Parameters) (s : ℝ) (x : Spacetime) :
    originalWickSquareMatrix a s vacuumCore vacuumCore x = 0 :=
  originalWickBilocalCore_vacuum a s x x

theorem originalWickSquareDistribution_vacuum (a : Parameters) (s : ℝ) :
    originalWickSquareDistribution a s vacuumCore vacuumCore = 0 := by
  ext h
  simp [originalWickSquareDistribution_pairing, originalWickSquareMatrix_vacuum]

end AASCKleinGordon
