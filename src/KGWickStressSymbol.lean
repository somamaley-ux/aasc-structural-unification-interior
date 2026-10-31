import KGWickCompactSmoothMetricTests

/-! Algebraic divergence symbol with the original Fourier coefficient.
Only the two separate shell equations are used; their sum is not on shell. -/
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
open scoped BigOperators
namespace AASCKleinGordon

def wickFourierDerivativeConstant : ℂ := -(2*Real.pi*Complex.I)

def wickEtaDot (p q : Spacetime) : ℂ :=
  ∑ i,(wickFlatSign i : ℂ)*(p i : ℂ)*(q i : ℂ)

def wickRaisedStressSymbol (a : Parameters) (p q : Spacetime) (i j : Fin 4) : ℂ :=
  (wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)*
    ((wickFourierDerivativeConstant^2/2)*((p i : ℂ)*(q j : ℂ)+(p j : ℂ)*(q i : ℂ))-
      ((wickFlatMetricComponent i j : ℂ)/2)*
        (wickFourierDerivativeConstant^2*wickEtaDot p q+(massWaveNumber a : ℂ)^2))

theorem wick_raised_stress_symbol_contraction (a : Parameters) (p q : Spacetime) (j : Fin 4) :
    (∑ i,wickFourierDerivativeConstant*((p i : ℂ)+(q i : ℂ))*wickRaisedStressSymbol a p q i j) =
      (wickFourierDerivativeConstant*(wickFlatSign j : ℂ)/2)*
        ((wickFourierDerivativeConstant^2*wickEtaDot p p-(massWaveNumber a : ℂ)^2)*(q j : ℂ)+
          (wickFourierDerivativeConstant^2*wickEtaDot q q-(massWaveNumber a : ℂ)^2)*(p j : ℂ)) := by
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hj with h|h|h|h <;> subst j <;>
    norm_num [wickRaisedStressSymbol,wickEtaDot,wickFlatSign,wickFlatMetricComponent,Fin.sum_univ_four] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num <;> ring

theorem wick_raised_stress_symbol_conserved (a : Parameters) (p q : Spacetime)
    (hp : wickFourierDerivativeConstant^2*wickEtaDot p p=(massWaveNumber a : ℂ)^2)
    (hq : wickFourierDerivativeConstant^2*wickEtaDot q q=(massWaveNumber a : ℂ)^2) (j : Fin 4) :
    (∑ i,wickFourierDerivativeConstant*((p i : ℂ)+(q i : ℂ))*wickRaisedStressSymbol a p q i j)=0 := by
  rw [wick_raised_stress_symbol_contraction,hp,hq]
  ring

end AASCKleinGordon
