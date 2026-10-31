import KGWickStressKernels

noncomputable section
set_option maxHeartbeats 8000000
open scoped SchwartzMap BigOperators
namespace AASCKleinGordon

def wickRaisedStressLocalMatrix (a : Parameters) (n : ℕ) (p q : ParticleConfiguration n → Spacetime)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (i j : Fin 4) : Spacetime → ℂ :=
  wickLocalMatrix a n (fun z => p z+q z) (wickRaisedStressKernel a n p q G i j)

theorem wick_raised_stress_local_smooth (a : Parameters) (n : ℕ)
    (p q : ParticleConfiguration n → Spacetime) (hp : p.HasTemperateGrowth) (hq : q.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (i j : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (wickRaisedStressLocalMatrix a n p q G i j) :=
  wickLocalMatrix_smooth a n _ (hp.add hq) _

theorem wick_raised_stress_local_formula (a : Parameters) (n : ℕ)
    (p q : ParticleConfiguration n → Spacetime) (hp : p.HasTemperateGrowth) (hq : q.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (i j : Fin 4) (x : Spacetime) :
    wickRaisedStressLocalMatrix a n p q G i j x=
      (wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)*
        ((1/2 : ℂ)*(wickLocalMatrix a n (fun z => p z+q z) (wickStressMixedKernel n p q G i j) x+
          wickLocalMatrix a n (fun z => p z+q z) (wickStressMixedKernel n p q G j i) x)-
          ((wickFlatMetricComponent i j : ℂ)/2)*
            (-wickLocalMatrix a n (fun z => p z+q z) (wickStressMixedKernel n p q G 0 0) x+
              wickLocalMatrix a n (fun z => p z+q z) (wickStressMixedKernel n p q G 1 1) x+
              wickLocalMatrix a n (fun z => p z+q z) (wickStressMixedKernel n p q G 2 2) x+
              wickLocalMatrix a n (fun z => p z+q z) (wickStressMixedKernel n p q G 3 3) x+
              (massWaveNumber a : ℂ)^2*wickLocalMatrix a n (fun z => p z+q z) G x)) := by
  unfold wickRaisedStressLocalMatrix
  have heq (H : 𝓢(ParticleConfiguration n,ℂ)) :
      wickLocalMatrix a n (fun z => p z+q z) H x=
        wickLocalKernelFunctional a n (fun z => p z+q z) x H :=
    (wickLocalKernelFunctional_apply a n (fun z => p z+q z) (hp.add hq) H x).symm
  simp_rw [heq]
  simp only [wickRaisedStressKernel,wickStressTraceKernel,map_smul,map_add,map_sub,map_neg,smul_eq_mul]

theorem wick_raised_stress_local_conserved (a : Parameters) (n : ℕ)
    (p q : ParticleConfiguration n → Spacetime) (hp : p.HasTemperateGrowth) (hq : q.HasTemperateGrowth)
    (hsp : ∀ z,wickFourierDerivativeConstant^2*wickEtaDot (p z) (p z)=(massWaveNumber a : ℂ)^2)
    (hsq : ∀ z,wickFourierDerivativeConstant^2*wickEtaDot (q z) (q z)=(massWaveNumber a : ℂ)^2)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (j : Fin 4) (x : Spacetime) :
    (∑ i,fderiv ℝ (wickRaisedStressLocalMatrix a n p q G i j) x (spacetimeCoordinateVector i))=0 := by
  let ω : ParticleConfiguration n → Spacetime := fun z => p z+q z
  have hω : ω.HasTemperateGrowth := hp.add hq
  let L := wickLocalKernelFunctional a n ω x
  have hzero : (∑ i,wickDirectionalStateKernel n ω (spacetimeCoordinateVector i)
      (wickRaisedStressKernel a n p q G i j))=0 := by
    apply SchwartzMap.ext
    intro z
    simp only [SchwartzMap.sum_apply,SchwartzMap.zero_apply,wickDirectionalStateKernel_apply n ω hω,
      wick_directional_coordinate_coefficient,wick_raised_stress_kernel_apply a n p q hp hq]
    change (∑ i,wickFourierDerivativeConstant*((p z+q z) i : ℂ)*
      (wickRaisedStressSymbol a (p z) (q z) i j*G z))=0
    simp only [PiLp.add_apply,Complex.ofReal_add]
    calc
      _ = (∑ i,wickFourierDerivativeConstant*((p z i : ℂ)+(q z i : ℂ))*
          wickRaisedStressSymbol a (p z) (q z) i j)*G z := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [wick_raised_stress_symbol_conserved a (p z) (q z) (hsp z) (hsq z)]; simp
  calc
    _ = ∑ i,L (wickDirectionalStateKernel n ω (spacetimeCoordinateVector i)
        (wickRaisedStressKernel a n p q G i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change fderiv ℝ (wickLocalMatrix a n ω (wickRaisedStressKernel a n p q G i j)) x
        (spacetimeCoordinateVector i)=L _
      rw [wickLocalMatrix_directional_fderiv a n ω hω]
      exact (wickLocalKernelFunctional_apply a n ω hω _ x).symm
    _ = L (∑ i,wickDirectionalStateKernel n ω (spacetimeCoordinateVector i)
        (wickRaisedStressKernel a n p q G i j)) := (map_sum L _ _).symm
    _ = 0 := by rw [hzero,map_zero]

end AASCKleinGordon
