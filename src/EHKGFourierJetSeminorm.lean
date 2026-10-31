import EHKGFourierJetBounds

/-! A continuous source seminorm bounds every derivative, uniformly in
spacetime. The graph weight is smooth (a sum of squared norms), so its
Schwartz multiplier and L1 inclusion are actual continuous linear maps. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

def graphJetWeight (sigma : KGSpatialSpace → Spacetime) (n : ℕ) (z : KGSpatialSpace) : ℝ :=
  (1 + ‖sigma z‖ ^ 2 + ‖z‖ ^ 2) ^ n

theorem graph_jet_weight_temperate (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) : (graphJetWeight sigma n).HasTemperateGrowth :=
  (((Function.HasTemperateGrowth.const 1).add
    ((Function.hasTemperateGrowth_norm_sq Spacetime).comp growth)).add
      (Function.hasTemperateGrowth_norm_sq KGSpatialSpace)).pow n

def graphJetWeightSchwartzCLM (sigma : KGSpatialSpace → Spacetime) (n : ℕ) :
    𝓢(KGSpatialSpace, ℂ) →L[ℂ] 𝓢(KGSpatialSpace, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun z => (graphJetWeight sigma n z : ℂ))

def graphJetWeightL1CLM (sigma : KGSpatialSpace → Spacetime) (n : ℕ) :
    𝓢(KGSpatialSpace, ℂ) →L[ℝ] Lp ℂ 1 (volume : Measure KGSpatialSpace) :=
  (SchwartzMap.toLpCLM ℝ ℂ 1 volume).comp ((graphJetWeightSchwartzCLM sigma n).restrictScalars ℝ)

theorem graph_jet_weight_schwartz_norm (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) (z : KGSpatialSpace) :
    ‖graphJetWeightSchwartzCLM sigma n G z‖ = graphJetWeight sigma n z * ‖G z‖ := by
  have complexGrowth : (fun z : KGSpatialSpace => (graphJetWeight sigma n z : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (graph_jet_weight_temperate sigma growth n)
  rw [graphJetWeightSchwartzCLM, SchwartzMap.smulLeftCLM_apply_apply complexGrowth, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by dsimp [graphJetWeight]; positivity)]

theorem graph_jet_weight_l1_norm (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    ‖graphJetWeightL1CLM sigma n G‖ = ∫ z : KGSpatialSpace, graphJetWeight sigma n z * ‖G z‖ := by
  rw [graphJetWeightL1CLM, ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [(graphJetWeightSchwartzCLM sigma n G).coeFn_toLp 1 volume] with z hz
  change ‖(graphJetWeightSchwartzCLM sigma n G).toLp 1 volume z‖ = _
  rw [hz, graph_jet_weight_schwartz_norm sigma growth]

theorem graph_moment_integral_le_weight_l1 (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    (∫ z : KGSpatialSpace, ‖volumeFrequencyGraph sigma z‖ ^ n * ‖G z‖) ≤ ‖graphJetWeightL1CLM sigma n G‖ := by
  rw [graph_jet_weight_l1_norm sigma growth]
  have weightIntegrable : Integrable (fun z : KGSpatialSpace => graphJetWeight sigma n z * ‖G z‖) := by
    simpa only [graph_jet_weight_schwartz_norm sigma growth] using (graphJetWeightSchwartzCLM sigma n G).integrable.norm
  apply integral_mono (volume_graph_moments_integrable n sigma growth G) weightIntegrable
  intro z
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  change max ‖sigma z‖ ‖z‖ ≤ 1 + ‖sigma z‖ ^ 2 + ‖z‖ ^ 2
  apply max_le
  · nlinarith [sq_nonneg (‖sigma z‖ - 1), sq_nonneg ‖z‖]
  · nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg ‖sigma z‖]

theorem volume_phase_uniform_jet_seminorm_bound (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (G : 𝓢(KGSpatialSpace, ℂ)) (n : ℕ) (x : Spacetime) :
    ‖iteratedFDeriv ℝ n (volumePhaseIntegral sigma G) x‖ ≤
      (2 * Real.pi * ‖volumeGraphPairing‖) ^ n * ‖graphJetWeightL1CLM sigma n G‖ :=
  (volume_phase_iterated_derivative_bound sigma growth G n x).trans
    (mul_le_mul_of_nonneg_left (graph_moment_integral_le_weight_l1 sigma growth n G) (by positivity))

theorem graph_jet_source_seminorm_continuous (sigma : KGSpatialSpace → Spacetime) (n : ℕ) :
    Continuous (fun G : 𝓢(KGSpatialSpace, ℂ) => ‖graphJetWeightL1CLM sigma n G‖) :=
  (graphJetWeightL1CLM sigma n).continuous.norm

end AASCKleinGordon.CurvedKG
