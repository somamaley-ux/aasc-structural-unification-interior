import KGWickStressSymbol

noncomputable section
set_option maxHeartbeats 8000000
namespace AASCKleinGordon

theorem wick_stress_shell_of_kleinGordon (a : Parameters) (p : Spacetime)
    (hp : kleinGordonSymbol a p=0) :
    wickFourierDerivativeConstant^2*wickEtaDot p p=(massWaveNumber a : ℂ)^2 := by
  have hc := congrArg Complex.ofReal hp
  simp only [kleinGordonSymbol,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_zero] at hc
  norm_num at hc
  have hk : wickFourierDerivativeConstant^2 = -((2*Real.pi : ℝ) : ℂ)^2 := by
    dsimp [wickFourierDerivativeConstant]
    push_cast
    calc
      _ = ((2*Real.pi : ℂ)^2)*Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hk]
  norm_num [wickEtaDot,wickFlatSign,Fin.sum_univ_four] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num
  linear_combination -hc

theorem wick_stress_shellFrequency (a : Parameters) (p : Momentum) :
    wickFourierDerivativeConstant^2*wickEtaDot (shellFrequency a p) (shellFrequency a p)=
      (massWaveNumber a : ℂ)^2 :=
  wick_stress_shell_of_kleinGordon a _ (kleinGordonSymbol_on_shell a p)

theorem wick_stress_neg_shellFrequency (a : Parameters) (p : Momentum) :
    wickFourierDerivativeConstant^2*wickEtaDot (-shellFrequency a p) (-shellFrequency a p)=
      (massWaveNumber a : ℂ)^2 :=
  wick_stress_shell_of_kleinGordon a _ (by rw [kleinGordonSymbol_neg,kleinGordonSymbol_on_shell])

theorem wick_core_frequency0_stress_shell (a : Parameters) (n : ℕ) (i : Fin 4)
    (z : ParticleConfiguration (n+2)) :
    wickFourierDerivativeConstant^2*wickEtaDot (wickCoreChannelFrequency0 a n i z)
      (wickCoreChannelFrequency0 a n i z)=(massWaveNumber a : ℂ)^2 := by
  fin_cases i
  · change wickFourierDerivativeConstant^2*wickEtaDot (shellFrequency a (z (0 : Fin (n+2))))
      (shellFrequency a (z (0 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_shellFrequency a (z (0 : Fin (n+2)))
  · change wickFourierDerivativeConstant^2*wickEtaDot (shellFrequency a (z (0 : Fin (n+2))))
      (shellFrequency a (z (0 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_shellFrequency a (z (0 : Fin (n+2)))
  · change wickFourierDerivativeConstant^2*wickEtaDot (-shellFrequency a (z (1 : Fin (n+2))))
      (-shellFrequency a (z (1 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_neg_shellFrequency a (z (1 : Fin (n+2)))
  · change wickFourierDerivativeConstant^2*wickEtaDot (-shellFrequency a (z (1 : Fin (n+2))))
      (-shellFrequency a (z (1 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_neg_shellFrequency a (z (1 : Fin (n+2)))

theorem wick_core_frequency1_stress_shell (a : Parameters) (n : ℕ) (i : Fin 4)
    (z : ParticleConfiguration (n+2)) :
    wickFourierDerivativeConstant^2*wickEtaDot (wickCoreChannelFrequency1 a n i z)
      (wickCoreChannelFrequency1 a n i z)=(massWaveNumber a : ℂ)^2 := by
  fin_cases i
  · change wickFourierDerivativeConstant^2*wickEtaDot (shellFrequency a (z (1 : Fin (n+2))))
      (shellFrequency a (z (1 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_shellFrequency a (z (1 : Fin (n+2)))
  · change wickFourierDerivativeConstant^2*wickEtaDot (-shellFrequency a (z (1 : Fin (n+2))))
      (-shellFrequency a (z (1 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_neg_shellFrequency a (z (1 : Fin (n+2)))
  · change wickFourierDerivativeConstant^2*wickEtaDot (shellFrequency a (z (0 : Fin (n+2))))
      (shellFrequency a (z (0 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_shellFrequency a (z (0 : Fin (n+2)))
  · change wickFourierDerivativeConstant^2*wickEtaDot (-shellFrequency a (z (0 : Fin (n+2))))
      (-shellFrequency a (z (0 : Fin (n+2))))=(massWaveNumber a : ℂ)^2
    exact wick_stress_neg_shellFrequency a (z (0 : Fin (n+2)))

end AASCKleinGordon
