import KGWickOriginalSectorBilocalAttachment

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

def wickOriginalCCBilocalSector (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration (n+2),ℂ)) (v : 𝓢(ParticleConfiguration n,ℂ))
    (x y : Spacetime) : ℂ :=
  wickBilocalMatrix a (n+2) (wickShellFrequencyAt a n 0)
    (wickShellFrequencyAt a n 1) (conjugateSchwartzCLM (wickAAStateKernel n v u)) x y

theorem wickOriginalCCBilocalSector_smearing (a : Parameters) (n : ℕ)
    (u : bosonicSchwartz (n+2)) (v : bosonicSchwartz n) (h k : 𝓢(Spacetime,ℂ)) :
    ((Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+2) : ℂ)) *
      (∫ x,h x * ∫ y,k y * wickOriginalCCBilocalSector a n u.val v.val x y) =
      star (inner ℂ (bosonicCoreToSector a n v)
        (bosonicCoreToSector a n
          (annihilationSectorCLM a n (spacetimeSmearingCLM a k)
            (annihilationSectorCLM a (n+1) (spacetimeSmearingCLM a h) u)))) := by
  rw [wickAA_kernel_eq_original_bosonic_annihilations]
  unfold wickOriginalCCBilocalSector
  rw [wickBilocalMatrix_product_test_pairing a (n+2) _ _
    (wickShellFrequencyAt_temperate a n 0) (wickShellFrequencyAt_temperate a n 1)]
  have hi : star (∫ z, star (spacetimeSmearingCLM a h (z 0)) *
        star (spacetimeSmearingCLM a k (z 1)) * wickAAStateKernel n v.val u.val z
          ∂particleMeasure a (n+2)) =
      ∫ z,(𝓕 h) (shellFrequency a (z 0)) * (𝓕 k) (shellFrequency a (z 1)) *
        star (wickAAStateKernel n v.val u.val z) ∂particleMeasure a (n+2) := by
    calc
      _ = ∫ z, star (star (spacetimeSmearingCLM a h (z 0)) *
          star (spacetimeSmearingCLM a k (z 1)) * wickAAStateKernel n v.val u.val z)
            ∂particleMeasure a (n+2) := integral_conj.symm
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          simp only [star_mul, star_star, spacetimeSmearingCLM_apply]
          ring
  simp only [star_mul]
  rw [hi]
  change _ * (∫ z, (𝓕 h) (shellFrequency a (z 0)) * (𝓕 k) (shellFrequency a (z 1)) *
      star (wickAAStateKernel n v.val u.val z) ∂particleMeasure a (n+2)) = _
  simp only [RCLike.star_def, Complex.conj_ofReal]
  ring

theorem wickOriginalCCBilocalSector_diagonal (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration (n+2),ℂ)) (v : 𝓢(ParticleConfiguration n,ℂ)) (x : Spacetime) :
    wickOriginalCCBilocalSector a n u v x x =
      wickLocalMatrix a (n+2)
        (fun z => shellFrequency a (z 0) + shellFrequency a (z 1))
        (conjugateSchwartzCLM (wickAAStateKernel n v u)) x := by
  rw [wickOriginalCCBilocalSector, wickBilocalMatrix_diagonal a (n+2) _ _
    (wickShellFrequencyAt_temperate a n 1)]
  rfl

theorem wickOriginalCCBilocalSector_diagonal_smooth (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration (n+2),ℂ)) (v : 𝓢(ParticleConfiguration n,ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => wickOriginalCCBilocalSector a n u v x x) := by
  simp_rw [wickOriginalCCBilocalSector_diagonal]
  exact wickLocalMatrix_smooth a (n+2) _
    ((wickShellFrequencyAt_temperate a n 0).add (wickShellFrequencyAt_temperate a n 1)) _

end AASCKleinGordon
