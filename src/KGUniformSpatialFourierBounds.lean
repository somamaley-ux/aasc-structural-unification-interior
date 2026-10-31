import KGSpacetimeSpatialBessel
import KGInverseFourierFamilies
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon

theorem spatialFourier_apply (f : 𝓢(KGSpatialSpace,ℂ)) (ξ : KGSpatialSpace) :
    𝓕 f ξ=∫ x, spatialFourierKernel (-ξ) x*f x := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [spatialFourierKernel,inner_neg_right,smul_eq_mul]
    congr 2
    push_cast
    ring

theorem spatialSlice_zero_outside_ball (h : 𝓢(Spacetime,ℂ)) (R t : ℝ)
    (hs : tsupport (h : Spacetime → ℂ) ⊆ Metric.closedBall 0 R)
    (x : KGSpatialSpace) (hx : x ∉ Metric.closedBall 0 R) :
    spacetimeSpatialSliceCLM t h x=0 := by
  change h (spacetimeSpatialJoin (t,x))=0
  apply image_eq_zero_of_notMem_tsupport
  intro hh
  have hn : ‖spacetimeSpatialJoin (t,x)‖ ≤ R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hs hh
  exact hx (by simpa only [Metric.mem_closedBall,dist_zero_right] using (norm_spatial_le_join t x).trans hn)

theorem spatialSlice_fourier_uniform_bound (h : 𝓢(Spacetime,ℂ)) (R : ℝ)
    (hs : tsupport (h : Spacetime → ℂ) ⊆ Metric.closedBall 0 R) (t : ℝ) (ξ : KGSpatialSpace) :
    ‖𝓕 (spacetimeSpatialSliceCLM t h) ξ‖ ≤
      SchwartzMap.seminorm ℝ 0 0 h*(volume : Measure KGSpatialSpace).real (Metric.closedBall 0 R) := by
  rw [spatialFourier_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall 0 R) (by
    intro x hx
    rw [spatialSlice_zero_outside_ball h R t hs x hx,mul_zero])]
  apply norm_setIntegral_le_of_norm_le_const (isCompact_closedBall (0 : KGSpatialSpace) R).measure_lt_top
  intro x hx
  rw [norm_mul,spatialFourierKernel_norm,one_mul]
  exact h.norm_le_seminorm ℝ _

theorem spatialSlice_fourier_uniform_decay (h : 𝓢(Spacetime,ℂ)) (R : ℝ)
    (hs : tsupport (h : Spacetime → ℂ) ⊆ Metric.closedBall 0 R) (t : ℝ) (ξ : KGSpatialSpace) :
    ‖𝓕 (spacetimeSpatialSliceCLM t h) ξ‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 (spacetimeSpatialBessel (spacetimeSpatialBessel h))*
        (volume : Measure KGSpatialSpace).real (Metric.closedBall 0 R))/(spatialBesselWeight ξ)^2 := by
  have hb := spatialSlice_fourier_uniform_bound (spacetimeSpatialBessel (spacetimeSpatialBessel h)) R
    ((spacetimeSpatialBessel_twice_tsupport_subset h).trans hs) t ξ
  rw [fourier_spacetimeSpatialBessel_twice_slice,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (spatialBesselWeight_pos ξ)] at hb
  apply (le_div_iff₀ (sq_pos_of_pos (spatialBesselWeight_pos ξ))).mpr
  simpa only [mul_comm] using hb

/-- Joint measurability/continuity is obtained after the spatial Fourier integral,
using a fixed compact spatial majorant. This does not exchange a raw momentum/x integral. -/
theorem spatialSlice_fourier_joint_continuous (h : 𝓢(Spacetime,ℂ)) (R : ℝ)
    (hs : tsupport (h : Spacetime → ℂ) ⊆ Metric.closedBall 0 R) :
    Continuous (fun z : ℝ × KGSpatialSpace => 𝓕 (spacetimeSpatialSliceCLM z.1 h) z.2) := by
  simp_rw [spatialFourier_apply]
  let B := (Metric.closedBall (0 : KGSpatialSpace) R).indicator
    (fun _ : KGSpatialSpace => SchwartzMap.seminorm ℝ 0 0 h)
  apply continuous_of_dominated (bound := B)
  · intro z
    exact (spatialFourierKernel_mul_integrable (spacetimeSpatialSliceCLM z.1 h) (-z.2)).aestronglyMeasurable
  · intro z
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.closedBall (0 : KGSpatialSpace) R
      · rw [norm_mul,spatialFourierKernel_norm,one_mul]
        simpa only [B,Set.indicator_of_mem hx] using h.norm_le_seminorm ℝ (spacetimeSpatialJoin (z.1,x))
      · rw [spatialSlice_zero_outside_ball h R z.1 hs x hx,mul_zero,norm_zero]
        simp only [B,Set.indicator_of_notMem hx,le_refl]
  · exact (integrableOn_const ((isCompact_closedBall (0 : KGSpatialSpace) R).measure_ne_top)).integrable_indicator
      (isCompact_closedBall (0 : KGSpatialSpace) R).measurableSet
  · exact Eventually.of_forall fun x =>
      ((spatialFourierKernel_continuous_left x).comp continuous_snd.neg).mul
        (h.continuous.comp (spacetimeSpatialJoin.continuous.comp (continuous_fst.prodMk continuous_const)))

end AASCKleinGordon
