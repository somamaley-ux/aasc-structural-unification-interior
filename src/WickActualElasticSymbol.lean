import WickActualForwardKernel

noncomputable section
set_option maxHeartbeats 2500000
open scoped BigOperators SchwartzMap
namespace AASCKleinGordon

/-- The off-diagonal identity for the actual mixed-channel symbol, including
its original hbar coefficient. No generalized-state normalization is inferred. -/
theorem wick_actual_mixed_symbol_elastic_tensor (a : Parameters) (p q : Momentum)
    (i j : Fin 4) :
    2*(a.hbar : ℂ)^2*wickRaisedStressSymbol a (shellFrequency a p) (-shellFrequency a q) i j =
      (scalarMatrixElement a (massShell a p) (massShell a q) i j : ℂ) := by
  have hh : (a.hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr a.hbar_pos.ne'
  have hf : (fourierWaveScale a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (fourierWaveScale_pos a).ne'
  have hk : wickFourierDerivativeConstant^2 =
      -(a.hbar : ℂ)⁻¹^2/(fourierWaveScale a : ℂ)^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hf)).mpr
    linear_combination -wick_original_fourier_shell_square a
  have hc2 (v : ℝ) (r : Momentum) : (Fin.cons v r : Fin 4 → ℝ) 2=r 1 := rfl
  have hc3 (v : ℝ) (r : Momentum) : (Fin.cons v r : Fin 4 → ℝ) 3=r 2 := rfl
  fin_cases i <;> fin_cases j <;>
    simp [wickRaisedStressSymbol,wickEtaDot,wickFlatSign,wickFlatMetricComponent,
      shellFrequency_apply,massShell,scalarMatrixElement,minkowskiMetric,metricSign,
      minkowskiDot,massWaveNumber,Fin.sum_univ_four,hk,hc2,hc3] <;>
    push_cast <;> field_simp [hh,hf] <;> ring

theorem wick_actual_CA_kernel_elastic_tensor (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2)) (i j : Fin 4) :
    2*(a.hbar : ℂ)^2*(wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 1)
      (wickCoreChannelFrequency1 a n 1) G i j z) =
        (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*G z := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 1) (wickCoreChannelFrequency1_temperate a n 1)]
  change 2*(a.hbar : ℂ)^2*(wickRaisedStressSymbol a (shellFrequency a (z 0))
    (-shellFrequency a (z 1)) i j*G z)=_
  rw [← mul_assoc,wick_actual_mixed_symbol_elastic_tensor]

theorem wick_actual_reversed_CA_kernel_elastic_tensor (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (z : ParticleConfiguration (n+2)) (i j : Fin 4) :
    2*(a.hbar : ℂ)^2*(wickRaisedStressKernel a (n+2) (wickCoreChannelFrequency0 a n 2)
      (wickCoreChannelFrequency1 a n 2) G i j z) =
        (scalarMatrixElement a (massShell a (z 0)) (massShell a (z 1)) i j : ℂ)*G z := by
  rw [wick_raised_stress_kernel_apply a (n+2) _ _
    (wickCoreChannelFrequency0_temperate a n 2) (wickCoreChannelFrequency1_temperate a n 2)]
  change 2*(a.hbar : ℂ)^2*(wickRaisedStressSymbol a (-shellFrequency a (z 1))
    (shellFrequency a (z 0)) i j*G z)=_
  rw [wick_same_stress_symbol_swap,← mul_assoc,wick_actual_mixed_symbol_elastic_tensor]

end AASCKleinGordon
