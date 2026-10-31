import WickPhysicalPairMarginal

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped SchwartzMap
namespace AASCKleinGordon
open SchwartzOperations

variable {E F V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem wick_coordinate_partial_slice_integrable (μ : Measure E) [μ.HasTemperateGrowth]
    (T : E ≃L[ℝ] V) (H : 𝓢(E × F,ℂ)) (y : F) : Integrable (fun x => H (x,y)) μ := by
  have hi := weighted_slice_integrable (wick_coordinate_partial_weight_integrable μ T)
    (SchwartzMap.smulLeftCLM ℂ (fun z : E × F => wickCoordinatePartialPolynomial μ T z.1) H) y
  convert hi using 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (wick_coordinate_partial_polynomial_temperate μ T)]
  simp only [smul_eq_mul,wickCoordinatePartialWeight,← mul_assoc,
    inv_mul_cancel₀ (wick_coordinate_partial_nonzero μ T x),one_mul]

theorem wick_physical_pair_spectator_integrable (a : Parameters) (n : ℕ)
    (G : 𝓢(ParticleConfiguration (n+2),ℂ)) (p q : Momentum) :
    Integrable (fun r => G (Fin.cons p (Fin.cons q r))) (particleMeasure a n) := by
  have hi := wick_coordinate_partial_slice_integrable (particleMeasure a n) (wickConfigurationEuclidean n)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (wickJoinVisiblePair n) G) (p,q)
  exact hi

end AASCKleinGordon
