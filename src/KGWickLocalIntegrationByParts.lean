import KGOriginalWickStressConservation

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem wick_local_directional_derivative_test_integrable (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x*fderiv ℝ (wickLocalMatrix a n ω G) x d) := by
  simp_rw [wickLocalMatrix_directional_fderiv a n ω hω]
  exact wickLocalMatrix_test_integrable a n ω hω.1.continuous _ h

theorem wick_local_directional_test_pairing (a : Parameters) (n : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x*fderiv ℝ (wickLocalMatrix a n ω G) x d)=
      -(∫ x,wickDirectionalTestCLM d h x*wickLocalMatrix a n ω G x) := by
  simp_rw [wickLocalMatrix_directional_fderiv a n ω hω]
  rw [wickLocalMatrix_test_pairing a n ω hω.1.continuous,
    wickLocalMatrix_test_pairing a n ω hω.1.continuous,
    wickKernelEvaluationCLM_apply,wickKernelEvaluationCLM_apply,← integral_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [wickDirectionalStateKernel_apply n ω hω,wickDirectionalTestCLM_fourier]
    unfold wickDirectionalCoefficient
    rw [real_inner_comm d (ω z)]
    ring)

theorem wick_core_stress_directional_test_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k i j : Fin 4) (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x*fderiv ℝ (wickCoreRaisedStressMatrix a n u v k i j) x d) :=
  wick_local_directional_derivative_test_integrable a (n+2) _
    ((wickCoreChannelFrequency0_temperate a n k).add (wickCoreChannelFrequency1_temperate a n k)) _ d h

theorem wick_core_stress_test_integrable (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    Integrable (fun x => h x*wickCoreRaisedStressMatrix a n u v k i j x) :=
  wickLocalMatrix_test_integrable a (n+2) _
    (((wickCoreChannelFrequency0_temperate a n k).add (wickCoreChannelFrequency1_temperate a n k)).1.continuous) _ h

theorem wick_core_stress_directional_test_pairing (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (k i j : Fin 4) (d : Spacetime) (h : 𝓢(Spacetime,ℂ)) :
    (∫ x,h x*fderiv ℝ (wickCoreRaisedStressMatrix a n u v k i j) x d)=
      -(∫ x,wickDirectionalTestCLM d h x*wickCoreRaisedStressMatrix a n u v k i j x) :=
  wick_local_directional_test_pairing a (n+2) _
    ((wickCoreChannelFrequency0_temperate a n k).add (wickCoreChannelFrequency1_temperate a n k)) _ d h

end AASCKleinGordon
