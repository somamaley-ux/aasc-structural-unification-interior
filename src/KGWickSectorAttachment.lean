import KGWickStateKernels
import KGBosonicAdjointness

/-! Exact original-sector contraction identities. These attach the new state
coefficient to actual original contractions; no local-distribution bridge is
received as an assumption. -/
noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem wickAA_kernel_integrable_with_original_smears (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (u : 𝓢(ParticleConfiguration n,ℂ))
    (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    Integrable (fun z => star (g (z 0)) * star (f (z 1)) * wickAAStateKernel n u v z)
      (particleMeasure a (n+2)) := by
  have hi := schwartz_pair_integrable (particleMeasure a (n+2))
    (particleTensorInsertCLM (n+1) g (particleTensorInsertCLM n f u)) v
  convert hi using 1
  funext z
  simp only [particleTensorInsertCLM_apply, wickAAStateKernel_apply, star_mul]
  rw [show Fin.tail z 0 = z 1 from rfl]
  ring

theorem wickAA_kernel_eq_original_double_contraction (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (u : 𝓢(ParticleConfiguration n,ℂ))
    (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    inner ℂ (particleSchwartzToHilbert a n u)
      (particleSchwartzToHilbert a n
        (particleContractionCLM a n f (particleContractionCLM a (n+1) g v))) =
      ∫ z, star (g (z 0)) * star (f (z 1)) * wickAAStateKernel n u v z
        ∂particleMeasure a (n+2) := by
  rw [← particle_tensor_contraction_adjoint a n f u
    (particleContractionCLM a (n+1) g v),
    ← particle_tensor_contraction_adjoint a (n+1) g (particleTensorInsertCLM n f u) v,
    particle_schwartz_inner_eq]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [particleTensorInsertCLM_apply, wickAAStateKernel_apply, star_mul]
    rw [show Fin.tail z 0 = z 1 from rfl]
    ring

theorem wickAA_kernel_eq_original_bosonic_annihilations (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (u : bosonicSchwartz n) (v : bosonicSchwartz (n+2)) :
    inner ℂ (bosonicCoreToSector a n u)
      (bosonicCoreToSector a n
        (annihilationSectorCLM a n f (annihilationSectorCLM a (n+1) g v))) =
      ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ)) *
        ∫ z, star (g (z 0)) * star (f (z 1)) * wickAAStateKernel n u.val v.val z
          ∂particleMeasure a (n+2) := by
  change inner ℂ (particleSchwartzToHilbert a n u.val)
    (particleSchwartzToHilbert a n
      (annihilationSectorCLM a n f (annihilationSectorCLM a (n+1) g v)).val) = _
  simp only [annihilationSector_val, map_smul, inner_smul_right,
    wickAA_kernel_eq_original_double_contraction]
  have hn : ((n+1 : ℕ) : ℝ)+1 = (n : ℝ)+2 := by push_cast; ring
  rw [hn]
  ring

end AASCKleinGordon
