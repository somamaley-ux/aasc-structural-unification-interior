import KGWickBilocalMatrix
import KGWickLocalSectorDerivatives
import KGWickSectorAttachment
import KGWickMixedAttachment
import SchwartzFourierConjugation

/-! Actual original sector bilocal matrix coefficients and their proved local
diagonals. Original creation/annihilation smearing, shell, Wigner measure and
particle-number normalization are used throughout. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

def wickShellFrequencyAt (a : Parameters) (n : ℕ) (i : Fin (n+2))
    (z : ParticleConfiguration (n+2)) : Spacetime := shellFrequency a (z i)

theorem wickShellFrequencyAt_temperate (a : Parameters) (n : ℕ) (i : Fin (n+2)) :
    (wickShellFrequencyAt a n i).HasTemperateGrowth :=
  (shellFrequency_temperate a).comp
    (ContinuousLinearMap.proj (R:=ℝ) i : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth

theorem original_annihilation_smear_fourier (a : Parameters) (h : 𝓢(Spacetime,ℂ)) (p : Momentum) :
    star (spacetimeSmearingCLM a (conjugateSchwartzCLM h) p) =
      (𝓕 h) (-shellFrequency a p) := by
  simp only [spacetimeSmearingCLM_apply, fourier_conjugateSchwartz_apply, star_star]

def wickOriginalAABilocalSector (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ))
    (x y : Spacetime) : ℂ :=
  wickBilocalMatrix a (n+2) (-wickShellFrequencyAt a n 1)
    (-wickShellFrequencyAt a n 0) (wickAAStateKernel n u v) x y

def wickOriginalMixedBilocalSector (a : Parameters) (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) (x y : Spacetime) : ℂ :=
  wickBilocalMatrix a (n+2) (wickShellFrequencyAt a n 0)
    (-wickShellFrequencyAt a n 1) (wickMixedStateKernel n u v) x y

theorem wickOriginalAABilocalSector_smearing (a : Parameters) (n : ℕ)
    (u : bosonicSchwartz n) (v : bosonicSchwartz (n+2)) (h k : 𝓢(Spacetime,ℂ)) :
    ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ)) *
      (∫ x, h x * ∫ y, k y * wickOriginalAABilocalSector a n u.val v.val x y) =
    inner ℂ (bosonicCoreToSector a n u)
      (bosonicCoreToSector a n
        (annihilationSectorCLM a n (spacetimeSmearingCLM a (conjugateSchwartzCLM h))
          (annihilationSectorCLM a (n+1)
            (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v))) := by
  rw [wickAA_kernel_eq_original_bosonic_annihilations]
  unfold wickOriginalAABilocalSector
  rw [wickBilocalMatrix_product_test_pairing a (n+2) _ _
    (wickShellFrequencyAt_temperate a n 1).neg (wickShellFrequencyAt_temperate a n 0).neg]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [Pi.neg_apply, wickShellFrequencyAt]
    rw [original_annihilation_smear_fourier, original_annihilation_smear_fourier]
    ring

theorem wickOriginalMixedBilocalSector_smearing (a : Parameters) (n : ℕ)
    (u v : bosonicSchwartz (n+1)) (h k : 𝓢(Spacetime,ℂ)) :
    ((n+1 : ℝ) : ℂ) *
      (∫ x, h x * ∫ y, k y * wickOriginalMixedBilocalSector a n u.val v.val x y) =
    inner ℂ
      (bosonicCoreToSector a n (annihilationSectorCLM a n (spacetimeSmearingCLM a h) u))
      (bosonicCoreToSector a n (annihilationSectorCLM a n
        (spacetimeSmearingCLM a (conjugateSchwartzCLM k)) v)) := by
  rw [wickMixed_kernel_eq_original_bosonic_annihilations]
  unfold wickOriginalMixedBilocalSector
  rw [wickBilocalMatrix_product_test_pairing a (n+2) _ _
    (wickShellFrequencyAt_temperate a n 0) (wickShellFrequencyAt_temperate a n 1).neg]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only [wickShellFrequencyAt]
    rw [original_annihilation_smear_fourier]
    rfl

theorem wickOriginalAABilocalSector_diagonal (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ)) (x : Spacetime) :
    wickOriginalAABilocalSector a n u v x x =
      wickLocalMatrix a (n+2) (wickAAShellFrequency a n) (wickAAStateKernel n u v) x := by
  rw [wickOriginalAABilocalSector, wickBilocalMatrix_diagonal a (n+2) _ _
    (wickShellFrequencyAt_temperate a n 0).neg]
  have he : (fun z => (-wickShellFrequencyAt a n 1) z + (-wickShellFrequencyAt a n 0) z) =
      wickAAShellFrequency a n := by
    funext z
    simp only [Pi.neg_apply, wickShellFrequencyAt, wickAAShellFrequency]
    abel
  rw [he]

theorem wickOriginalMixedBilocalSector_diagonal (a : Parameters) (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) (x : Spacetime) :
    wickOriginalMixedBilocalSector a n u v x x =
      wickLocalMatrix a (n+2) (wickMixedShellFrequency a n) (wickMixedStateKernel n u v) x := by
  rw [wickOriginalMixedBilocalSector, wickBilocalMatrix_diagonal a (n+2) _ _
    (wickShellFrequencyAt_temperate a n 1).neg]
  rfl

end AASCKleinGordon
