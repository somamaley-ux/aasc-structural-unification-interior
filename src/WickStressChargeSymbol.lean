import KGSignedShellStress

/-! Necessary hypersurface-charge identities for the SAME original stress
symbol. These do not assume a hypersurface integral or charge normalization. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace AASCKleinGordon

theorem wick_fourier_derivative_constant_ne_zero : wickFourierDerivativeConstant≠0 := by
  simp [wickFourierDerivativeConstant,Real.pi_ne_zero,Complex.I_ne_zero]

theorem wick_eta_dot_neg_right (p q : Spacetime) :
    wickEtaDot p (-q) = -wickEtaDot p q := by
  simp [wickEtaDot,Finset.sum_neg_distrib]

theorem wick_same_stress_mixed_diagonal_symbol (a : Parameters) (p : Spacetime)
    (shell : wickFourierDerivativeConstant^2*wickEtaDot p p=(massWaveNumber a : ℂ)^2)
    (i j : Fin 4) :
    wickRaisedStressSymbol a p (-p) i j=
      -(wickFourierDerivativeConstant^2)*(wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)*
        (p i : ℂ)*(p j : ℂ) := by
  have traceZero : wickFourierDerivativeConstant^2*wickEtaDot p (-p)+(massWaveNumber a : ℂ)^2=0 := by
    rw [wick_eta_dot_neg_right]
    linear_combination -shell
  have hneg (k : Fin 4) : ((-p) k : ℂ)=-(p k : ℂ) := by
    change ((-(p k) : ℝ) : ℂ)=_
    exact Complex.ofReal_neg _
  simp only [wickRaisedStressSymbol,traceZero,mul_zero,sub_zero,hneg]
  ring

theorem wick_original_shell_mixed_diagonal_symbol (a : Parameters) (p : Momentum)
    (i j : Fin 4) :
    wickRaisedStressSymbol a (shellFrequency a p) (-shellFrequency a p) i j=
      -(wickFourierDerivativeConstant^2)*(wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)*
        (shellFrequency a p i : ℂ)*(shellFrequency a p j : ℂ) :=
  wick_same_stress_mixed_diagonal_symbol a _ (wick_stress_shellFrequency a p) i j

theorem wick_same_stress_spatial_diagonal_row_zero (a : Parameters) (p q : Spacetime)
    (hp : wickFourierDerivativeConstant^2*wickEtaDot p p=(massWaveNumber a : ℂ)^2)
    (hq : wickFourierDerivativeConstant^2*wickEtaDot q q=(massWaveNumber a : ℂ)^2)
    (spatial : ∀ i : Fin 3,p i.succ+q i.succ=0) (time : p 0+q 0≠0)
    (j : Fin 4) : wickRaisedStressSymbol a p q 0 j=0 := by
  have ward := wick_raised_stress_symbol_conserved a p q hp hq j
  rw [Fin.sum_univ_succ] at ward
  have hsum : (∑ i : Fin 3,wickFourierDerivativeConstant*
      ((p i.succ : ℂ)+(q i.succ : ℂ))*wickRaisedStressSymbol a p q i.succ j)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hz : (p i.succ : ℂ)+(q i.succ : ℂ)=0 := by
      simpa only [Complex.ofReal_add,Complex.ofReal_zero] using congrArg Complex.ofReal (spatial i)
    rw [hz,mul_zero,zero_mul]
  rw [hsum,add_zero] at ward
  have ht : (p 0 : ℂ)+(q 0 : ℂ)≠0 := by
    intro h
    apply time
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_add,Complex.ofReal_zero] using h
  exact (mul_eq_zero.mp ward).resolve_left (mul_ne_zero wick_fourier_derivative_constant_ne_zero ht)

end AASCKleinGordon
