import KGWickLocalSmoothness

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 101] secondCountableTopologyEither_of_left
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon

theorem wickAAShellFrequency_temperate (a : Parameters) (n : ℕ) :
    (wickAAShellFrequency a n).HasTemperateGrowth :=
  (((shellFrequency_temperate a).comp
    (ContinuousLinearMap.proj (R:=ℝ) 0 : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth).add
   ((shellFrequency_temperate a).comp
    (ContinuousLinearMap.proj (R:=ℝ) 1 : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth)).neg

theorem wickMixedShellFrequency_temperate (a : Parameters) (n : ℕ) :
    (wickMixedShellFrequency a n).HasTemperateGrowth :=
  ((shellFrequency_temperate a).comp
    (ContinuousLinearMap.proj (R:=ℝ) 0 : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth).sub
   ((shellFrequency_temperate a).comp
    (ContinuousLinearMap.proj (R:=ℝ) 1 : ParticleConfiguration (n+2) →L[ℝ] Momentum).hasTemperateGrowth)

theorem wick_graph_measure_moments (a : Parameters) (n k : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) :
    Integrable (fun t : Spacetime × ParticleConfiguration n => ‖t‖^k * ‖G t.2‖)
      (Measure.map (wickFrequencyGraph n ω) (particleMeasure a n)) :=
  (integrable_map_measure
    (((continuous_norm.pow k).mul (G.continuous.comp continuous_snd).norm).aestronglyMeasurable)
    (show AEMeasurable (wickFrequencyGraph n ω) (particleMeasure a n) from
      (hω.1.continuous.prodMk continuous_id).aemeasurable)).mpr
    (wick_graph_moments_integrable a n k ω hω G)

theorem wickLocalMatrix_iteratedFDeriv (a : Parameters) (n k : ℕ)
    (ω : ParticleConfiguration n → Spacetime) (hω : ω.HasTemperateGrowth)
    (G : 𝓢(ParticleConfiguration n,ℂ)) (x : Spacetime) :
    iteratedFDeriv ℝ k (wickLocalMatrix a n ω G) x =
      ∫ z, Real.fourierChar (-inner ℝ x (ω z)) •
        VectorFourier.fourierPowSMulRight (wickGraphPairing n)
          (fun t : Spacetime × ParticleConfiguration n => G t.2)
          (wickFrequencyGraph n ω z) k ∂particleMeasure a n := by
  rw [wickLocalMatrix_eq_graph_fourier a n ω hω.1.continuous G]
  rw [VectorFourier.iteratedFDeriv_fourierIntegral (wickGraphPairing n)
    (N:=⊤) (fun j hj => wick_graph_measure_moments a n j ω hω G)
    ((G.continuous.comp continuous_snd).aestronglyMeasurable) (by simp : (k : ℕ∞)≤⊤)]
  rw [VectorFourier.fourierIntegral]
  have he : Continuous (wickFrequencyGraph n ω) := hω.1.continuous.prodMk continuous_id
  rw [integral_map he.aemeasurable]
  · apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change Real.fourierChar (-inner ℝ (ω z) x) • _ =
        Real.fourierChar (-inner ℝ x (ω z)) • _
      rw [real_inner_comm x (ω z)]
  · exact ((Real.continuous_fourierChar.comp
      (((wickGraphPairing n).flip x).continuous.neg)).smul
        ((G.continuous.comp continuous_snd).fourierPowSMulRight (wickGraphPairing n) k)).aestronglyMeasurable

theorem wickAALocalSectorMatrix_smooth (a : Parameters) (n : ℕ)
    (u : 𝓢(ParticleConfiguration n,ℂ)) (v : 𝓢(ParticleConfiguration (n+2),ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (wickLocalMatrix a (n+2) (wickAAShellFrequency a n) (wickAAStateKernel n u v)) :=
  wickLocalMatrix_smooth a (n+2) _ (wickAAShellFrequency_temperate a n) _

theorem wickMixedLocalSectorMatrix_smooth (a : Parameters) (n : ℕ)
    (u v : 𝓢(ParticleConfiguration (n+1),ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (wickLocalMatrix a (n+2) (wickMixedShellFrequency a n) (wickMixedStateKernel n u v)) :=
  wickLocalMatrix_smooth a (n+2) _ (wickMixedShellFrequency_temperate a n) _

end AASCKleinGordon
