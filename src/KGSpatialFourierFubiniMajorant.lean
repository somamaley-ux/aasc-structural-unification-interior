import KGUniformSpatialFourierBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon

theorem abs_time_le_spacetimeSpatialJoin (t : ℝ) (x : KGSpatialSpace) :
    |t| ≤ ‖spacetimeSpatialJoin (t,x)‖ := by
  nlinarith [spacetimeSpatialJoin_norm_sq t x,sq_abs t,sq_nonneg ‖x‖,
    abs_nonneg t,norm_nonneg (spacetimeSpatialJoin (t,x))]

theorem spatialSlice_zero_outside_time_interval (h : 𝓢(Spacetime,ℂ)) (R t : ℝ)
    (hs : tsupport (h : Spacetime → ℂ) ⊆ Metric.closedBall 0 R) (ht : t ∉ Icc (-R) R) :
    spacetimeSpatialSliceCLM t h=0 := by
  ext x
  change h (spacetimeSpatialJoin (t,x))=0
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  have hn : ‖spacetimeSpatialJoin (t,x)‖ ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hs hz
  exact ht (abs_le.mp ((abs_time_le_spacetimeSpatialJoin t x).trans hn))

def spatialFourierDecayMajorant (ξ : KGSpatialSpace) : ℝ := ((1+‖ξ‖^2)^2)⁻¹

theorem spatialFourierDecayMajorant_integrable : Integrable spatialFourierDecayMajorant := by
  have hi := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure KGSpatialSpace))
    (r := (4 : ℝ)) (by norm_num [finrank_euclideanSpace] : (Module.finrank ℝ KGSpatialSpace : ℝ)<4)
  have he (ξ : KGSpatialSpace) : (1+‖ξ‖^2)^(-(4 : ℝ)/2)=spatialFourierDecayMajorant ξ := by
    rw [show (-(4 : ℝ)/2)=-(2 : ℝ) by norm_num,Real.rpow_neg (by positivity),Real.rpow_two]
    rfl
  simpa only [he] using hi

theorem spatialBesselWeight_inv_sq_le_majorant (ξ : KGSpatialSpace) :
    ((spatialBesselWeight ξ)^2)⁻¹ ≤ spatialFourierDecayMajorant ξ := by
  have hp : 1 ≤ (2*Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  have hw : 1+‖ξ‖^2 ≤ spatialBesselWeight ξ := by
    unfold spatialBesselWeight
    nlinarith [sq_nonneg ‖ξ‖]
  unfold spatialFourierDecayMajorant
  apply (inv_le_inv₀ (sq_pos_of_pos (spatialBesselWeight_pos ξ))
    (by positivity : 0 < (1+‖ξ‖^2)^2)).mpr
  nlinarith [spatialBesselWeight_pos ξ,norm_nonneg ξ]

theorem compact_spatialSlice_fourier_integrable
    (h : 𝓢(Spacetime,ℂ)) (hc : HasCompactSupport (h : Spacetime → ℂ)) :
    Integrable (fun z : ℝ × KGSpatialSpace => 𝓕 (spacetimeSpatialSliceCLM z.1 h) z.2) := by
  obtain ⟨R,hR,hs⟩ := hc.isBounded.subset_closedBall_lt 0 (0 : Spacetime)
  let C := SchwartzMap.seminorm ℝ 0 0 (spacetimeSpatialBessel (spacetimeSpatialBessel h))*
    (volume : Measure KGSpatialSpace).real (Metric.closedBall 0 R)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let T := (Icc (-R) R).indicator (fun _ : ℝ => C)
  have hT : Integrable T := (integrableOn_const (isCompact_Icc.measure_ne_top)).integrable_indicator measurableSet_Icc
  have hprod := hT.mul_prod spatialFourierDecayMajorant_integrable
  apply hprod.mono' (spatialSlice_fourier_joint_continuous h R hs).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rcases z with ⟨t,ξ⟩
    change ‖𝓕 (spacetimeSpatialSliceCLM t h) ξ‖ ≤ T t*spatialFourierDecayMajorant ξ
    by_cases ht : t ∈ Icc (-R) R
    · rw [show T t=C from Set.indicator_of_mem ht _]
      have hb := spatialSlice_fourier_uniform_decay h R hs t ξ
      change ‖𝓕 (spacetimeSpatialSliceCLM t h) ξ‖ ≤ C/(spatialBesselWeight ξ)^2 at hb
      exact hb.trans (by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (spatialBesselWeight_inv_sq_le_majorant ξ) hC)
    · rw [spatialSlice_zero_outside_time_interval h R t hs ht,FourierTransform.fourier_zero,SchwartzMap.zero_apply]
      simp only [T,Set.indicator_of_notMem ht,zero_mul,le_refl,norm_zero]

end AASCKleinGordon
