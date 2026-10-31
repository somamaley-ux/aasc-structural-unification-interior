import KGSignedShellStress

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

def wickLocalKernelFunctional (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (x : Spacetime) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (particleMeasure a n)).comp
    (SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω x))

theorem wickLocalKernelFunctional_apply (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x : Spacetime) :
    wickLocalKernelFunctional a n ω x G=wickLocalMatrix a n ω G x := by
  change (∫ z,(SchwartzMap.smulLeftCLM ℂ (wickPhaseCoefficient n ω x) G) z ∂particleMeasure a n)=_
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (wickPhaseCoefficient_temperate n ω hω x)]
    rfl)

def wickStressMixedKernel (n : ℕ) (p q : ParticleConfiguration n → Spacetime)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (i j : Fin 4) : 𝓢(ParticleConfiguration n,ℂ) :=
  wickDirectionalStateKernel n q (spacetimeCoordinateVector j)
    (wickDirectionalStateKernel n p (spacetimeCoordinateVector i) G)

def wickStressTraceKernel (a : Parameters) (n : ℕ) (p q : ParticleConfiguration n → Spacetime)
    (G : 𝓢(ParticleConfiguration n,ℂ)) : 𝓢(ParticleConfiguration n,ℂ) :=
  -wickStressMixedKernel n p q G 0 0+wickStressMixedKernel n p q G 1 1+
    wickStressMixedKernel n p q G 2 2+wickStressMixedKernel n p q G 3 3+
    (massWaveNumber a : ℂ)^2 • G

def wickRaisedStressKernel (a : Parameters) (n : ℕ) (p q : ParticleConfiguration n → Spacetime)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (i j : Fin 4) : 𝓢(ParticleConfiguration n,ℂ) :=
  ((wickFlatSign i : ℂ)*(wickFlatSign j : ℂ)) •
    ((1/2 : ℂ) • (wickStressMixedKernel n p q G i j+wickStressMixedKernel n p q G j i)-
      ((wickFlatMetricComponent i j : ℂ)/2) • wickStressTraceKernel a n p q G)

theorem wick_directional_coordinate_coefficient (n : ℕ) (p : ParticleConfiguration n → Spacetime)
    (i : Fin 4) (z : ParticleConfiguration n) :
    wickDirectionalCoefficient n p (spacetimeCoordinateVector i) z=
      wickFourierDerivativeConstant*(p z i : ℂ) := by
  simp [wickDirectionalCoefficient,wickFourierDerivativeConstant,spacetimeCoordinateVector,
    EuclideanSpace.inner_single_left]

theorem wick_stress_mixed_kernel_apply (n : ℕ) (p q : ParticleConfiguration n → Spacetime)
    (hp : p.HasTemperateGrowth) (hq : q.HasTemperateGrowth) (G : 𝓢(ParticleConfiguration n,ℂ))
    (i j : Fin 4) (z : ParticleConfiguration n) :
    wickStressMixedKernel n p q G i j z=
      wickFourierDerivativeConstant^2*(p z i : ℂ)*(q z j : ℂ)*G z := by
  unfold wickStressMixedKernel
  rw [wickDirectionalStateKernel_apply n q hq,wickDirectionalStateKernel_apply n p hp]
  simp_rw [wick_directional_coordinate_coefficient]
  ring

theorem wick_raised_stress_kernel_apply (a : Parameters) (n : ℕ)
    (p q : ParticleConfiguration n → Spacetime) (hp : p.HasTemperateGrowth) (hq : q.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (i j : Fin 4) (z : ParticleConfiguration n) :
    wickRaisedStressKernel a n p q G i j z=wickRaisedStressSymbol a (p z) (q z) i j*G z := by
  simp only [wickRaisedStressKernel,wickStressTraceKernel,SchwartzMap.smul_apply,
    SchwartzMap.sub_apply,SchwartzMap.add_apply,SchwartzMap.neg_apply,smul_eq_mul,
    wick_stress_mixed_kernel_apply n p q hp hq]
  norm_num [wickRaisedStressSymbol,wickEtaDot,wickFlatSign,Fin.sum_univ_four] <;>
    (try simp only [Fin.ext_iff]) <;> norm_num <;> ring

end AASCKleinGordon
