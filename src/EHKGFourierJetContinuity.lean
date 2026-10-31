import EHKGFourierJetSeminorm
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Continuous dependence in the uniform topology of every actual spacetime
derivative of the phase integral. The source has its Schwartz topology;
it is not equipped with an invented norm or a closed-graph certificate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory
open scoped SchwartzMap FourierTransform Topology BoundedContinuousFunction
namespace AASCKleinGordon.CurvedKG

theorem volume_phase_add (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (G H : 𝓢(KGSpatialSpace, ℂ)) :
    volumePhaseIntegral sigma (G + H) = volumePhaseIntegral sigma G + volumePhaseIntegral sigma H := by
  funext x
  have integrablePhase (F : 𝓢(KGSpatialSpace, ℂ)) :
      Integrable (fun z => Real.fourierChar (-inner ℝ x (sigma z)) • F z) := by
    apply F.integrable.mono
    · exact ((Real.continuous_fourierChar.comp
        ((continuous_const.inner growth.1.continuous).neg)).smul F.continuous).aestronglyMeasurable
    · exact ae_of_all _ fun z => (Circle.norm_smul _ _).le
  change (∫ z, Real.fourierChar (-inner ℝ x (sigma z)) • (G z + H z)) = _
  simp_rw [smul_add]
  exact integral_add (integrablePhase G) (integrablePhase H)

theorem volume_phase_real_smul (sigma : KGSpatialSpace → Spacetime)
    (c : ℝ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    volumePhaseIntegral sigma (c • G) = c • volumePhaseIntegral sigma G := by
  funext x
  change (∫ z, Real.fourierChar (-inner ℝ x (sigma z)) • (c • G z)) = _
  simp_rw [smul_comm _ c]
  exact integral_smul c _

def volumePhaseJetBCF (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    Spacetime →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin n => Spacetime) ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (iteratedFDeriv ℝ n (volumePhaseIntegral sigma G))
    ((volume_phase_smooth sigma growth G).continuous_iteratedFDeriv (by exact_mod_cast le_top))
    ((2 * Real.pi * ‖volumeGraphPairing‖) ^ n * ‖graphJetWeightL1CLM sigma n G‖)
    (volume_phase_uniform_jet_seminorm_bound sigma growth G n)

def volumePhaseJetLinearMap (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) :
    𝓢(KGSpatialSpace, ℂ) →ₗ[ℝ]
      (Spacetime →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin n => Spacetime) ℂ) where
  toFun := volumePhaseJetBCF sigma growth n
  map_add' G H := by
    apply BoundedContinuousFunction.ext
    intro x
    change iteratedFDeriv ℝ n (volumePhaseIntegral sigma (G + H)) x = _
    rw [volume_phase_add sigma growth]
    exact iteratedFDeriv_add_apply
      (((volume_phase_smooth sigma growth G).of_le (by exact_mod_cast le_top)).contDiffAt)
      (((volume_phase_smooth sigma growth H).of_le (by exact_mod_cast le_top)).contDiffAt)
  map_smul' c G := by
    apply BoundedContinuousFunction.ext
    intro x
    change iteratedFDeriv ℝ n (volumePhaseIntegral sigma (c • G)) x = _
    rw [volume_phase_real_smul]
    exact iteratedFDeriv_const_smul_apply
      (((volume_phase_smooth sigma growth G).of_le (by exact_mod_cast le_top)).contDiffAt)

theorem volume_phase_jet_norm_bound (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    ‖volumePhaseJetLinearMap sigma growth n G‖ ≤
      (2 * Real.pi * ‖volumeGraphPairing‖) ^ n * ‖graphJetWeightL1CLM sigma n G‖ := by
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
  · positivity
  · exact volume_phase_uniform_jet_seminorm_bound sigma growth G n

theorem volume_phase_jet_continuous (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) :
    Continuous (volumePhaseJetLinearMap sigma growth n) := by
  apply continuous_of_continuousAt_zero (volumePhaseJetLinearMap sigma growth n)
  change Tendsto (volumePhaseJetLinearMap sigma growth n) (𝓝 0)
    (𝓝 (volumePhaseJetLinearMap sigma growth n 0))
  rw [map_zero]
  apply (_root_.tendsto_zero_iff_norm_tendsto_zero
    (f := fun G : 𝓢(KGSpatialSpace, ℂ) => volumePhaseJetLinearMap sigma growth n G)).mpr
  apply squeeze_zero (fun G => norm_nonneg _) (volume_phase_jet_norm_bound sigma growth n)
  simpa using (((graph_jet_source_seminorm_continuous sigma n).continuousAt
    (x := (0 : 𝓢(KGSpatialSpace, ℂ)))).const_mul
    ((2 * Real.pi * ‖volumeGraphPairing‖) ^ n))

def volumePhaseJetCLM (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (n : ℕ) :
    𝓢(KGSpatialSpace, ℂ) →L[ℝ]
      (Spacetime →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin n => Spacetime) ℂ) :=
  { volumePhaseJetLinearMap sigma growth n with
    cont := volume_phase_jet_continuous sigma growth n }

end AASCKleinGordon.CurvedKG
