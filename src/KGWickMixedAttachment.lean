import KGWickStateKernels
import KGBosonicAdjointness

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem wickMixed_smearMultiplier_temperate (n : ℕ) (f g : 𝓢(Momentum,ℂ)) :
    (fun z : ParticleConfiguration (n+2) => f (z 0) * star (g (z 1))).HasTemperateGrowth :=
  (f.hasTemperateGrowth.comp
    (ContinuousLinearMap.proj (R:=ℝ) 0 : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth).mul
  ((conjugateSchwartzCLM g).hasTemperateGrowth.comp
    (ContinuousLinearMap.proj (R:=ℝ) 1 : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth)

theorem wickMixed_kernel_integrable_with_original_smears (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) :
    Integrable (fun z => f (z 0) * star (g (z 1)) * wickMixedStateKernel n u v z)
      (particleMeasure a (n+2)) := by
  have hi := (SchwartzMap.smulLeftCLM ℂ
    (fun z : ParticleConfiguration (n+2) => f (z 0) * star (g (z 1)))
    (wickMixedStateKernel n u v)).integrable (μ:=particleMeasure a (n+2))
  convert hi using 1
  funext z
  rw [SchwartzMap.smulLeftCLM_apply_apply (wickMixed_smearMultiplier_temperate n f g)]
  rfl

theorem wickMixed_kernel_eq_original_contractions (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) :
    inner ℂ (particleSchwartzToHilbert a n (particleContractionCLM a n f u))
      (particleSchwartzToHilbert a n (particleContractionCLM a n g v)) =
      ∫ z, f (z 0) * star (g (z 1)) * wickMixedStateKernel n u v z
        ∂particleMeasure a (n+2) := by
  let I (z : ParticleConfiguration (n+2)) :=
    f (z 0) * star (g (z 1)) * wickMixedStateKernel n u v z
  have hI : Integrable I (particleMeasure a (n+2)) :=
    wickMixed_kernel_integrable_with_original_smears a n f g u v
  have hJ : Integrable (fun z : Momentum × ParticleConfiguration (n+1) =>
      I (joinParticleCoordinates (n+1) z))
      ((wignerMeasure a).prod (particleMeasure a (n+1))) :=
    (joinParticleCoordinates_measurePreserving a (n+1)).integrable_comp_of_integrable hI
  rw [← particle_tensor_contraction_adjoint a n g (particleContractionCLM a n f u) v,
    particle_schwartz_inner_eq]
  calc
    _ = ∫ r, ∫ p, I (joinParticleCoordinates (n+1) (p,r))
        ∂wignerMeasure a ∂particleMeasure a (n+1) := by
      apply integral_congr_ae
      exact ae_of_all _ fun r => by
        simp only [particleTensorInsertCLM_apply, particleContractionCLM_apply]
        have hc : star (∫ p, star (f p) * u (Fin.cons p (Fin.tail r)) ∂wignerMeasure a) =
            ∫ p, star (star (f p) * u (Fin.cons p (Fin.tail r))) ∂wignerMeasure a := by
          exact integral_conj.symm
        rw [star_mul, hc, ← integral_mul_const, ← integral_mul_const]
        apply integral_congr_ae
        exact ae_of_all _ fun p => by
          simp only [I, joinParticleCoordinates_apply, wickMixedStateKernel_apply,
            Fin.cons_zero, Fin.tail_cons, star_mul, star_star]
          change _ = f p * star (g (r 0)) *
            (star (u (Fin.cons p (Fin.tail r))) * v r)
          ring
    _ = ∫ z : Momentum × ParticleConfiguration (n+1),
        I (joinParticleCoordinates (n+1) z)
          ∂(wignerMeasure a).prod (particleMeasure a (n+1)) :=
      (integral_prod_symm _ hJ).symm
    _ = _ := (joinParticleCoordinates_measurePreserving a (n+1)).integral_comp
      (joinParticleCoordinates (n+1)).toHomeomorph.measurableEmbedding I

theorem wickMixed_kernel_eq_original_bosonic_annihilations (a : Parameters) (n : ℕ)
    (f g : 𝓢(Momentum,ℂ)) (u v : bosonicSchwartz (n+1)) :
    inner ℂ (bosonicCoreToSector a n (annihilationSectorCLM a n f u))
      (bosonicCoreToSector a n (annihilationSectorCLM a n g v)) =
      ((n+1 : ℝ) : ℂ) * ∫ z, f (z 0) * star (g (z 1)) *
        wickMixedStateKernel n u.val v.val z ∂particleMeasure a (n+2) := by
  change inner ℂ
    (particleSchwartzToHilbert a n (annihilationSectorCLM a n f u).val)
    (particleSchwartzToHilbert a n (annihilationSectorCLM a n g v).val) = _
  rw [annihilationSector_val, annihilationSector_val, map_smul, map_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    wickMixed_kernel_eq_original_contractions]
  have hs : (Real.sqrt (n+1) : ℂ) * (Real.sqrt (n+1) : ℂ) = ((n+1 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  rw [← mul_assoc, hs]

end AASCKleinGordon
