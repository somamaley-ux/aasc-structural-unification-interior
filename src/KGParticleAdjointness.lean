import KGParticleProductTransport
import KGBosonicCCR
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

theorem schwartz_pair_integrable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
    (μ : Measure D) [μ.HasTemperateGrowth] (f g : 𝓢(D,ℂ)) :
    Integrable (fun x => star (f x) * g x) μ :=
  (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) g.hasTemperateGrowth
    (postcomposeCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ) f)).integrable

theorem particle_schwartz_inner_eq (a : Parameters) (n : ℕ)
    (H K : 𝓢(ParticleConfiguration n,ℂ)) :
    inner ℂ (particleSchwartzToHilbert a n H) (particleSchwartzToHilbert a n K) =
      ∫ y, star (H y) * K y ∂particleMeasure a n := by
  change inner ℂ (H.toLp 2 (particleMeasure a n)) (K.toLp 2 (particleMeasure a n)) = _
  simpa only [RCLike.inner_apply', RCLike.star_def] using
    SchwartzMap.inner_toL2_toL2_eq H K (particleMeasure a n)

theorem particle_tensor_contraction_adjoint (a : Parameters) (n : ℕ)
    (f : 𝓢(Momentum,ℂ)) (H : 𝓢(ParticleConfiguration n,ℂ))
    (K : 𝓢(ParticleConfiguration (n+1),ℂ)) :
    inner ℂ (particleSchwartzToHilbert a (n+1) (particleTensorInsertCLM n f H))
      (particleSchwartzToHilbert a (n+1) K) =
    inner ℂ (particleSchwartzToHilbert a n H)
      (particleSchwartzToHilbert a n (particleContractionCLM a n f K)) := by
  rw [particle_schwartz_inner_eq, particle_schwartz_inner_eq]
  let I (y : ParticleConfiguration (n+1)) := star (particleTensorInsertCLM n f H y) * K y
  have hI : Integrable I (particleMeasure a (n+1)) :=
    schwartz_pair_integrable _ (particleTensorInsertCLM n f H) K
  have hJ : Integrable (fun z : Momentum × ParticleConfiguration n =>
      I (joinParticleCoordinates n z)) ((wignerMeasure a).prod (particleMeasure a n)) :=
    (joinParticleCoordinates_measurePreserving a n).integrable_comp_of_integrable hI
  calc
    _ = ∫ z : Momentum × ParticleConfiguration n, I (joinParticleCoordinates n z)
        ∂(wignerMeasure a).prod (particleMeasure a n) :=
      ((joinParticleCoordinates_measurePreserving a n).integral_comp
        (joinParticleCoordinates n).toHomeomorph.measurableEmbedding I).symm
    _ = ∫ y, ∫ p, I (joinParticleCoordinates n (p,y)) ∂wignerMeasure a ∂particleMeasure a n :=
      integral_prod_symm _ hJ
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ p, I (joinParticleCoordinates n (p,y)) ∂wignerMeasure a) =
          star (H y) * particleContractionCLM a n f K y
        rw [particleContractionCLM_apply, ← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun p => by
          dsimp [I]
          simp only [joinParticleCoordinates_apply, particleTensorInsertCLM_apply,
            Fin.cons_zero, Fin.tail_cons, star_mul, map_mul]
          ring

end AASCKleinGordon
