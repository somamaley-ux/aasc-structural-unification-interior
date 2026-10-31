import WickStressChargeShell
import KGWickStressKernels

noncomputable section
set_option maxHeartbeats 1000000
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon

theorem wick_same_stress_symbol_swap (a : Parameters) (p q : Spacetime) (i j : Fin 4) :
    wickRaisedStressSymbol a p q i j=wickRaisedStressSymbol a q p i j := by
  have dot : wickEtaDot p q=wickEtaDot q p := by
    unfold wickEtaDot
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold wickRaisedStressSymbol
  rw [dot]
  ring

theorem wick_original_CC_kernel_zero_spatial_transfer (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (spatial : ∀ i : Fin 3,shellFrequency a (z 0) i.succ+shellFrequency a (z 1) i.succ=0)
    (j : Fin 4) :
    wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 0)
      (wickCoreChannelFrequency1 a n 0) G 0 j z=0 := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 0) (wickCoreChannelFrequency1_temperate a n 0)]
  change wickRaisedStressSymbol a (shellFrequency a (z 0)) (shellFrequency a (z 1)) 0 j*G z=0
  rw [wick_original_CC_charge_row_zero a (z 0) (z 1) spatial,zero_mul]

theorem wick_original_AA_kernel_zero_spatial_transfer (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (spatial : ∀ i : Fin 3,(-shellFrequency a (z 1)) i.succ+(-shellFrequency a (z 0)) i.succ=0)
    (j : Fin 4) :
    wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 3)
      (wickCoreChannelFrequency1 a n 3) G 0 j z=0 := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 3) (wickCoreChannelFrequency1_temperate a n 3)]
  change wickRaisedStressSymbol a (-shellFrequency a (z 1)) (-shellFrequency a (z 0)) 0 j*G z=0
  rw [wick_original_AA_charge_row_zero a (z 1) (z 0) spatial,zero_mul]

theorem wick_original_CA_kernel_momentum_diagonal (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (diagonal : z 1=z 0) (i j : Fin 4) :
    wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
      (wickCoreChannelFrequency1 a n 1) G i j z=
        ((massShell a (z 0) i : ℂ)*(massShell a (z 0) j : ℂ)/(a.hbar : ℂ)^2)*G z := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 1) (wickCoreChannelFrequency1_temperate a n 1)]
  change wickRaisedStressSymbol a (shellFrequency a (z 0)) (-shellFrequency a (z 1)) i j*G z=_
  rw [diagonal,wick_original_same_stress_mixed_momentum_symbol]

theorem wick_original_reversed_CA_kernel_momentum_diagonal (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2))
    (diagonal : z 1=z 0) (i j : Fin 4) :
    wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
      (wickCoreChannelFrequency1 a n 2) G i j z=
        ((massShell a (z 0) i : ℂ)*(massShell a (z 0) j : ℂ)/(a.hbar : ℂ)^2)*G z := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 2) (wickCoreChannelFrequency1_temperate a n 2)]
  change wickRaisedStressSymbol a (-shellFrequency a (z 1)) (shellFrequency a (z 0)) i j*G z=_
  rw [diagonal,wick_same_stress_symbol_swap,wick_original_same_stress_mixed_momentum_symbol]

end AASCKleinGordon
