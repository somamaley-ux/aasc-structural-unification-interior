import KGOriginalWickBilocalCore

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

def wickCoreChannelOriginalSectorPair (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (h k : 𝓢(Spacetime,ℂ)) (i : Fin 4) : ℂ :=
  ![star (inner ℂ (bosonicCoreToSector a n (v n))
      (bosonicCoreToSector a n
        (annihilationSectorCLM a n (spacetimeSmearingCLM a k)
          (annihilationSectorCLM a (n+1) (spacetimeSmearingCLM a h) (u (n+2)))))),
    inner ℂ (bosonicCoreToSector a n
        (annihilationSectorCLM a n (spacetimeSmearingCLM a h) (u (n+1))))
      (bosonicCoreToSector a n (annihilationSectorCLM a n
        (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) (v (n+1)))),
    inner ℂ (bosonicCoreToSector a n
        (annihilationSectorCLM a n (spacetimeSmearingCLM a k) (u (n+1))))
      (bosonicCoreToSector a n (annihilationSectorCLM a n
        (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) (v (n+1)))),
    inner ℂ (bosonicCoreToSector a n (u n))
      (bosonicCoreToSector a n (annihilationSectorCLM a n
        (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
          (annihilationSectorCLM a (n+1)
            (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) (v (n+2)))))] i

theorem wickCoreChannel_smearing_eq_original (a : Parameters) (n : ℕ)
    (u v : FiniteParticleCore) (h k : 𝓢(Spacetime,ℂ)) (i : Fin 4) :
    wickCoreChannelCoefficient n i *
      (∫ x,h x * ∫ y,k y * wickCoreChannelMatrix a n u v i x y) =
      wickCoreChannelOriginalSectorPair a n u v h k i := by
  fin_cases i
  · exact wickOriginalCCBilocalSector_smearing a n (u (n+2)) (v n) h k
  · exact wickOriginalMixedBilocalSector_smearing a n (u (n+1)) (v (n+1)) h k
  · rw [wickCoreChannelMatrix_product_test_pairing]
    change ((n+1 : ℝ) : ℂ) * (∫ z,(𝓕 h) (-shellFrequency a (z 1)) *
        (𝓕 k) (shellFrequency a (z 0)) * wickMixedStateKernel n (u (n+1)).val (v (n+1)).val z
          ∂particleMeasure a (n+2)) = _
    change _ = inner ℂ (bosonicCoreToSector a n
        (annihilationSectorCLM a n (spacetimeSmearingCLM a k) (u (n+1))))
      (bosonicCoreToSector a n (annihilationSectorCLM a n
        (spacetimeSmearingCLM a (conjugateSchwartzCLM h)) (v (n+1))))
    rw [wickMixed_kernel_eq_original_bosonic_annihilations]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only
      rw [original_annihilation_smear_fourier]
      simp only [spacetimeSmearingCLM_apply]
      ring
  · exact wickOriginalAABilocalSector_smearing a n (u n) (v (n+2)) h k

end AASCKleinGordon
