import KGFockTranslationDerivative
import KGFockTranslationContinuity
import UnitaryExactGeneratorConverse
import KGFockEnergyClosure
import KGFockSpatialMomentumClosure

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace AASCKleinGordon

theorem physical_translation_coefficient_star (hbar : ℝ) :
    star (-Translation.coefficient hbar)=Translation.coefficient hbar := by
  simp [Translation.coefficient,neg_div]

theorem fockPhase_exactGenerator (a : Parameters)
    (v : ∀ n,ParticleConfiguration n → ℝ) (hv : ∀ n,Measurable (v n))
    (hi : ∀ n (σ : Equiv.Perm (Fin n)) x,v n (particlePermutation n σ x)=v n x) :
    GlobalCharge.ExactGenerator (Translation.coefficient a.hbar)
      (fockPhaseUnitary a v hv hi a.hbar) (fockRealMultiplication a v hv hi) := by
  constructor
  · intro f
    constructor
    · exact GlobalCharge.differentiable_orbit_mem_selfAdjoint_domain
        (Translation.coefficient a.hbar)
        (GlobalCharge.physical_generator_coefficient_nonzero a.hbar a.hbar_pos)
        (physical_translation_coefficient_star a.hbar)
        (fockPhaseUnitary a v hv hi a.hbar) (fockPhaseMultiplier_zero a v hv hi a.hbar)
        (fun t x => rfl) (fockRealMultiplication a v hv hi) (fockRealMultiplication_selfAdjoint a v hv hi)
        (fockPhase_hasDerivAt_zero a v hv hi a.hbar) f
    · intro hf
      exact (fockPhase_hasDerivAt_zero a v hv hi a.hbar ⟨f,hf⟩).differentiableAt
  · exact fockPhase_hasDerivAt_zero a v hv hi a.hbar

theorem fockSpatialTranslation_exactGenerator (a : Parameters) (j : Fin 3) :
    GlobalCharge.ExactGenerator (-Complex.I/(a.hbar : ℂ))
      (fockSpatialTranslation a j) (fockMaximalSpatialMomentum a j) :=
  fockPhase_exactGenerator a (fun n => totalMomentumCLM n j) (fun n => (totalMomentumCLM n j).measurable)
    (fun n => totalMomentum_particlePermutation n j)

theorem fockTimeTranslation_exactGenerator (a : Parameters) :
    GlobalCharge.ExactGenerator (-Complex.I/(a.hbar : ℂ))
      (fockTimeTranslation a) (fockMaximalEnergy a) :=
  fockPhase_exactGenerator a (particleTotalEnergy a) (fun n => (particleTotalEnergy_continuous a n).measurable)
    (particleTotalEnergy_particlePermutation a)

theorem fockSpatialTranslation_originalClosure_exactGenerator (a : Parameters) (j : Fin 3) :
    GlobalCharge.ExactGenerator (-Complex.I/(a.hbar : ℂ))
      (fockSpatialTranslation a j) (fockCoreSpatialCharge a j).closure := by
  rw [fockCoreSpatialCharge_closure_eq_maximal]
  exact fockSpatialTranslation_exactGenerator a j

theorem fockTimeTranslation_originalClosure_exactGenerator (a : Parameters) :
    GlobalCharge.ExactGenerator (-Complex.I/(a.hbar : ℂ))
      (fockTimeTranslation a) (fockCoreEnergy a).closure := by
  rw [fockCoreEnergy_closure_eq_maximal]
  exact fockTimeTranslation_exactGenerator a

end AASCKleinGordon
