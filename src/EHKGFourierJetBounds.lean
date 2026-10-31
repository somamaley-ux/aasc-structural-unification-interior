import EHKGFourierMomentSmooth

/-! Quantitative bounds for every actual spacetime Fourier derivative.
These are preparation for LF-to-smooth-compact-open continuity, not a claim
that pointwise continuity alone implies the required evolution topology. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

theorem volume_phase_iterated_derivative_bound (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (G : 𝓢(KGSpatialSpace, ℂ)) (n : ℕ) (x : Spacetime) :
    ‖iteratedFDeriv ℝ n (volumePhaseIntegral sigma G) x‖ ≤
      (2 * Real.pi * ‖volumeGraphPairing‖) ^ n *
        ∫ z : KGSpatialSpace, ‖volumeFrequencyGraph sigma z‖ ^ n * ‖G z‖ := by
  let graphMeasure := Measure.map (volumeFrequencyGraph sigma) volume
  let f : Spacetime × KGSpatialSpace → ℂ := fun z => G z.2
  have continuousGraph : Continuous (volumeFrequencyGraph sigma) := growth.1.continuous.prodMk continuous_id
  have measurable : AEStronglyMeasurable f graphMeasure := (G.continuous.comp continuous_snd).aestronglyMeasurable
  have moments (k : ℕ) (_ : (k : ℕ∞) ≤ ⊤) :
      Integrable (fun z : Spacetime × KGSpatialSpace => ‖z‖ ^ k * ‖f z‖) graphMeasure := by
    apply (integrable_map_measure
      (((continuous_norm.pow k).mul (G.continuous.comp continuous_snd).norm).aestronglyMeasurable)
      continuousGraph.aemeasurable).mpr
    exact volume_graph_moments_integrable k sigma growth G
  rw [volume_phase_eq_graph_fourier sigma growth.1.continuous G,
    VectorFourier.iteratedFDeriv_fourierIntegral volumeGraphPairing (N := ⊤) moments measurable
      (le_top : (n : ℕ∞) ≤ ⊤)]
  have integrableKernel := VectorFourier.integrable_fourierPowSMulRight volumeGraphPairing (moments n le_top) measurable
  calc
    _ ≤ ∫ z : Spacetime × KGSpatialSpace, ‖VectorFourier.fourierPowSMulRight volumeGraphPairing f z n‖ ∂graphMeasure :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ z : Spacetime × KGSpatialSpace,
        (2 * Real.pi * ‖volumeGraphPairing‖) ^ n * (‖z‖ ^ n * ‖f z‖) ∂graphMeasure := by
      apply integral_mono integrableKernel.norm ((moments n le_top).const_mul _)
      intro z
      simpa only [mul_assoc] using VectorFourier.norm_fourierPowSMulRight_le volumeGraphPairing f z n
    _ = (2 * Real.pi * ‖volumeGraphPairing‖) ^ n *
        (∫ z : Spacetime × KGSpatialSpace, ‖z‖ ^ n * ‖f z‖ ∂graphMeasure) := by
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      exact integral_map continuousGraph.aemeasurable
        (((continuous_norm.pow n).mul (G.continuous.comp continuous_snd).norm).aestronglyMeasurable)

end AASCKleinGordon.CurvedKG
