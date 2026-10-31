import WickStressChargeSymbol

noncomputable section
set_option maxHeartbeats 1000000
namespace AASCKleinGordon

theorem wick_original_shell_time_negative (a : Parameters) (p : Momentum) :
    shellFrequency a p 0<0 := by
  rw [shellFrequency_apply]
  change fourierWaveScale a * (-energy a p/a.speed)<0
  exact mul_neg_of_pos_of_neg (fourierWaveScale_pos a)
    (div_neg_of_neg_of_pos (neg_neg_of_pos (energy_pos a p)) a.speed_pos)

theorem wick_original_CC_charge_row_zero (a : Parameters) (p q : Momentum)
    (spatial : ∀ i : Fin 3,shellFrequency a p i.succ+shellFrequency a q i.succ=0)
    (j : Fin 4) : wickRaisedStressSymbol a (shellFrequency a p) (shellFrequency a q) 0 j=0 := by
  apply wick_same_stress_spatial_diagonal_row_zero a _ _
    (wick_stress_shellFrequency a p) (wick_stress_shellFrequency a q) spatial
  exact ne_of_lt (add_neg (wick_original_shell_time_negative a p) (wick_original_shell_time_negative a q))

theorem wick_original_AA_charge_row_zero (a : Parameters) (p q : Momentum)
    (spatial : ∀ i : Fin 3,(-shellFrequency a p) i.succ+(-shellFrequency a q) i.succ=0)
    (j : Fin 4) : wickRaisedStressSymbol a (-shellFrequency a p) (-shellFrequency a q) 0 j=0 := by
  apply wick_same_stress_spatial_diagonal_row_zero a _ _
    (wick_stress_neg_shellFrequency a p) (wick_stress_neg_shellFrequency a q) spatial
  change -shellFrequency a p 0+-shellFrequency a q 0≠0
  have hp := wick_original_shell_time_negative a p
  have hq := wick_original_shell_time_negative a q
  linarith

theorem wick_raised_original_shell_frequency (a : Parameters) (p : Momentum) (i : Fin 4) :
    (wickFlatSign i : ℂ)*(shellFrequency a p i : ℂ)=
      (fourierWaveScale a : ℂ)*(massShell a p i : ℂ) := by
  have hmass : massShell a p=Fin.cons (energy a p/a.speed) p := by
    funext k
    fin_cases k <;> rfl
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [shellFrequency_apply,hmass,Fin.cons_zero]
    norm_num [wickFlatSign]
    push_cast
    ring
  · simp only [shellFrequency_apply,hmass,Fin.cons_succ]
    have sign : wickFlatSign k.succ=1 := by simp [wickFlatSign]
    rw [sign]
    push_cast
    ring

theorem wick_original_fourier_shell_constant (a : Parameters) :
    wickFourierDerivativeConstant*(fourierWaveScale a : ℂ)=
      -Complex.I*(a.hbar : ℂ)⁻¹ := by
  have h := congrArg Complex.ofReal (two_pi_fourierWaveScale a)
  push_cast at h
  dsimp [wickFourierDerivativeConstant]
  linear_combination -Complex.I*h

theorem wick_original_fourier_shell_square (a : Parameters) :
    -(wickFourierDerivativeConstant^2)*(fourierWaveScale a : ℂ)^2=(a.hbar : ℂ)⁻¹^2 := by
  calc
    _ = -(wickFourierDerivativeConstant*(fourierWaveScale a : ℂ))^2 := by ring
    _ = _ := by rw [wick_original_fourier_shell_constant];simp [mul_pow,Complex.I_sq]

theorem wick_original_same_stress_mixed_momentum_symbol (a : Parameters) (p : Momentum)
    (i j : Fin 4) :
    wickRaisedStressSymbol a (shellFrequency a p) (-shellFrequency a p) i j=
      (massShell a p i : ℂ)*(massShell a p j : ℂ)/(a.hbar : ℂ)^2 := by
  calc
    _ = -(wickFourierDerivativeConstant^2)*
        ((wickFlatSign i : ℂ)*(shellFrequency a p i : ℂ))*
        ((wickFlatSign j : ℂ)*(shellFrequency a p j : ℂ)) := by
      rw [wick_original_shell_mixed_diagonal_symbol]
      ring
    _ = -(wickFourierDerivativeConstant^2)*
        ((fourierWaveScale a : ℂ)*(massShell a p i : ℂ))*
        ((fourierWaveScale a : ℂ)*(massShell a p j : ℂ)) := by
      rw [wick_raised_original_shell_frequency,wick_raised_original_shell_frequency]
    _ = (-(wickFourierDerivativeConstant^2)*(fourierWaveScale a : ℂ)^2)*
        (massShell a p i : ℂ)*(massShell a p j : ℂ) := by ring
    _ = _ := by rw [wick_original_fourier_shell_square];simp only [div_eq_mul_inv,inv_pow];ring

theorem wick_original_same_stress_mixed_charge_symbol (a : Parameters) (p : Momentum) (j : Fin 4) :
    wickRaisedStressSymbol a (shellFrequency a p) (-shellFrequency a p) 0 j=
      ((energy a p/a.speed : ℝ) : ℂ)*(massShell a p j : ℂ)/(a.hbar : ℂ)^2 := by
  simpa only [massShell,Matrix.cons_val_zero] using wick_original_same_stress_mixed_momentum_symbol a p 0 j

end AASCKleinGordon
