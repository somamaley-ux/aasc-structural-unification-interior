import EHKGFourierJetContinuity
import EHKGCoordinateCauchy
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Topology.ContinuousMap.Compact

/-! Actual compact-open continuity of every derivative after fixed smooth
weighting, linear coordinate transport and real projection. Compact sets are
arbitrary, and the source retains its actual Schwartz topology. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

def compactRealJet (F : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) F)
    (K : Compacts CoordinatePoint) (n : ℕ) :
    C(K, ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinatePoint) ℝ) :=
  ⟨fun p => iteratedFDeriv ℝ n F p,
    ((regular.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp continuous_subtype_val)⟩

def weightedPhaseField (sigma : KGSpatialSpace → Spacetime) (e : CoordinatePoint →L[ℝ] Spacetime)
    (P : ℂ →L[ℝ] ℝ) (w : CoordinatePoint → ℝ) (G : 𝓢(KGSpatialSpace, ℂ))
    (p : CoordinatePoint) : ℝ := w p * P (volumePhaseIntegral sigma G (e p))

theorem weighted_phase_smooth (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (e : CoordinatePoint →L[ℝ] Spacetime)
    (P : ℂ →L[ℝ] ℝ) (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (G : 𝓢(KGSpatialSpace, ℂ)) : ContDiff ℝ (⊤ : ℕ∞) (weightedPhaseField sigma e P w G) :=
  regular.mul (P.contDiff.comp ((volume_phase_smooth sigma growth G).comp e.contDiff))

theorem transported_phase_jet_bound (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (e : CoordinatePoint →L[ℝ] Spacetime)
    (P : ℂ →L[ℝ] ℝ) (G : 𝓢(KGSpatialSpace, ℂ)) (n : ℕ) (p : CoordinatePoint) :
    ‖iteratedFDeriv ℝ n (fun q => P (volumePhaseIntegral sigma G (e q))) p‖ ≤
      ‖P‖ * ((2 * Real.pi * ‖volumeGraphPairing‖) ^ n * ‖graphJetWeightL1CLM sigma n G‖) * ‖e‖ ^ n := by
  have phaseRegular := volume_phase_smooth sigma growth G
  have left := P.norm_iteratedFDeriv_comp_left
    ((phaseRegular.comp e.contDiff).contDiffAt (x := p)) (n := n) (by exact_mod_cast le_top)
  apply left.trans
  rw [e.iteratedFDeriv_comp_right phaseRegular p (by exact_mod_cast le_top)]
  calc
    ‖P‖ * ‖(iteratedFDeriv ℝ n (volumePhaseIntegral sigma G) (e p)).compContinuousLinearMap (fun _ => e)‖ ≤
        ‖P‖ * (‖iteratedFDeriv ℝ n (volumePhaseIntegral sigma G) (e p)‖ * ‖e‖ ^ n) := by
      gcongr
      exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq (by simp)
    _ = (‖P‖ * ‖iteratedFDeriv ℝ n (volumePhaseIntegral sigma G) (e p)‖) * ‖e‖ ^ n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (volume_phase_uniform_jet_seminorm_bound sigma growth G n (e p))
        (norm_nonneg P)) (by positivity)

def weightedPhaseJetControl (sigma : KGSpatialSpace → Spacetime)
    (e : CoordinatePoint →L[ℝ] Spacetime) (P : ℂ →L[ℝ] ℝ)
    (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (K : Compacts CoordinatePoint) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖compactRealJet w regular K i‖ *
    (‖P‖ * ((2 * Real.pi * ‖volumeGraphPairing‖) ^ (n - i) *
      ‖graphJetWeightL1CLM sigma (n - i) G‖) * ‖e‖ ^ (n - i))

theorem weighted_phase_jet_control_nonnegative (sigma : KGSpatialSpace → Spacetime)
    (e : CoordinatePoint →L[ℝ] Spacetime) (P : ℂ →L[ℝ] ℝ)
    (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (K : Compacts CoordinatePoint) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    0 ≤ weightedPhaseJetControl sigma e P w regular K n G := by
  unfold weightedPhaseJetControl
  positivity

theorem weighted_phase_jet_control_continuous (sigma : KGSpatialSpace → Spacetime)
    (e : CoordinatePoint →L[ℝ] Spacetime) (P : ℂ →L[ℝ] ℝ)
    (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (K : Compacts CoordinatePoint) (n : ℕ) :
    Continuous (weightedPhaseJetControl sigma e P w regular K n) := by
  unfold weightedPhaseJetControl
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul ((continuous_const.mul
    (continuous_const.mul (graph_jet_source_seminorm_continuous sigma (n - i)))).mul continuous_const)

theorem weighted_phase_jet_bound (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (e : CoordinatePoint →L[ℝ] Spacetime)
    (P : ℂ →L[ℝ] ℝ) (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (K : Compacts CoordinatePoint) (n : ℕ) (G : 𝓢(KGSpatialSpace, ℂ)) :
    ‖compactRealJet (weightedPhaseField sigma e P w G)
      (weighted_phase_smooth sigma growth e P w regular G) K n‖ ≤
        weightedPhaseJetControl sigma e P w regular K n G := by
  apply (ContinuousMap.norm_le _ (weighted_phase_jet_control_nonnegative sigma e P w regular K n G)).mpr
  intro p
  apply (norm_iteratedFDeriv_mul_le regular
    (P.contDiff.comp ((volume_phase_smooth sigma growth G).comp e.contDiff)) p
    (n := n) (by exact_mod_cast le_top)).trans
  apply Finset.sum_le_sum
  intro i hi
  gcongr
  · exact (compactRealJet w regular K i).norm_coe_le_norm p
  · exact transported_phase_jet_bound sigma growth e P G (n - i) p

def weightedPhaseJetLinearMap (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (e : CoordinatePoint →L[ℝ] Spacetime)
    (P : ℂ →L[ℝ] ℝ) (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (K : Compacts CoordinatePoint) (n : ℕ) :
    𝓢(KGSpatialSpace, ℂ) →ₗ[ℝ]
      C(K, ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinatePoint) ℝ) where
  toFun G := compactRealJet (weightedPhaseField sigma e P w G)
    (weighted_phase_smooth sigma growth e P w regular G) K n
  map_add' G H := by
    have equation : weightedPhaseField sigma e P w (G + H) =
        weightedPhaseField sigma e P w G + weightedPhaseField sigma e P w H := by
      funext p
      simp [weightedPhaseField, volume_phase_add sigma growth, map_add, mul_add]
    apply ContinuousMap.ext
    intro p
    change iteratedFDeriv ℝ n (weightedPhaseField sigma e P w (G + H)) p = _
    rw [equation]
    exact iteratedFDeriv_add_apply
      (((weighted_phase_smooth sigma growth e P w regular G).of_le (by exact_mod_cast le_top)).contDiffAt)
      (((weighted_phase_smooth sigma growth e P w regular H).of_le (by exact_mod_cast le_top)).contDiffAt)
  map_smul' c G := by
    have equation : weightedPhaseField sigma e P w (c • G) = c • weightedPhaseField sigma e P w G := by
      funext p
      change w p * P (volumePhaseIntegral sigma (c • G) (e p)) =
        c • (w p * P (volumePhaseIntegral sigma G (e p)))
      rw [volume_phase_real_smul]
      change w p * P (c • volumePhaseIntegral sigma G (e p)) = _
      rw [P.map_smul]
      simp only [smul_eq_mul]
      ring
    apply ContinuousMap.ext
    intro p
    change iteratedFDeriv ℝ n (weightedPhaseField sigma e P w (c • G)) p = _
    rw [equation]
    exact iteratedFDeriv_const_smul_apply
      (((weighted_phase_smooth sigma growth e P w regular G).of_le (by exact_mod_cast le_top)).contDiffAt)

theorem weighted_phase_jet_continuous (sigma : KGSpatialSpace → Spacetime)
    (growth : sigma.HasTemperateGrowth) (e : CoordinatePoint →L[ℝ] Spacetime)
    (P : ℂ →L[ℝ] ℝ) (w : CoordinatePoint → ℝ) (regular : ContDiff ℝ (⊤ : ℕ∞) w)
    (K : Compacts CoordinatePoint) (n : ℕ) :
    Continuous (weightedPhaseJetLinearMap sigma growth e P w regular K n) := by
  apply continuous_of_continuousAt_zero (weightedPhaseJetLinearMap sigma growth e P w regular K n)
  change Tendsto (weightedPhaseJetLinearMap sigma growth e P w regular K n) (𝓝 0)
    (𝓝 (weightedPhaseJetLinearMap sigma growth e P w regular K n 0))
  rw [map_zero]
  apply (_root_.tendsto_zero_iff_norm_tendsto_zero
    (f := fun G : 𝓢(KGSpatialSpace, ℂ) => weightedPhaseJetLinearMap sigma growth e P w regular K n G)).mpr
  apply squeeze_zero (fun G => norm_nonneg _) (weighted_phase_jet_bound sigma growth e P w regular K n)
  have h := (weighted_phase_jet_control_continuous sigma e P w regular K n).continuousAt
    (x := (0 : 𝓢(KGSpatialSpace, ℂ)))
  simpa [weightedPhaseJetControl] using h.tendsto

end AASCKleinGordon.CurvedKG
