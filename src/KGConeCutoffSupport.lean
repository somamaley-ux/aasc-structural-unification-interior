import KGSmoothConeCutoff
import KGCompactIntegralDifferentiation

noncomputable section
set_option maxHeartbeats 600000
open Set Metric
open scoped Topology
namespace AASCKleinGordon

theorem smoothTransition_deriv_zero_of_neg (y : ℝ) (hy : y < 0) :
    deriv Real.smoothTransition y=0 := by
  have hd : HasDerivAt Real.smoothTransition 0 y :=
    (hasDerivAt_const y 0).congr_of_eventuallyEq (by
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact Real.smoothTransition.zero_of_nonpos hz.le)
  exact hd.deriv

/-- A single compact spatial ball supports the cutoff and both of its first derivatives
on a closed time interval. Its radius uses the Euclidean spatial norm. -/
theorem smoothConeCutoff_uniform_support
    (δ R a b t : ℝ) (x₀ x : KGSpatialSpace) (ht : t ∈ Icc a b)
    (hx : x ∉ closedBall x₀ (R-a)) :
    smoothConeCutoff δ R t x₀ x=0 ∧
    smoothConeCutoffTimeDerivative δ R t x₀ x=0 ∧
    smoothConeCutoffGradient δ R t x₀ x=0 := by
  have hn : R-a < ‖x-x₀‖ := by simpa only [mem_closedBall,dist_eq_norm,not_le] using hx
  have harg : R-t-regularizedSpatialDistance δ x₀ x < 0 := by
    linarith [ht.1,norm_sub_le_regularizedDistance δ x₀ x]
  have hd : smoothConeCutoffTimeDerivative δ R t x₀ x=0 := by
    unfold smoothConeCutoffTimeDerivative
    rw [smoothTransition_deriv_zero_of_neg _ harg,neg_zero]
  exact ⟨Real.smoothTransition.zero_of_nonpos harg.le,hd,by simp [smoothConeCutoffGradient,hd]⟩

theorem smoothConeCutoff_hasCompactSupport (δ R t : ℝ) (x₀ : KGSpatialSpace) :
    HasCompactSupport (smoothConeCutoff δ R t x₀) :=
  compactSupport_of_zero_outside_compact (isCompact_closedBall x₀ (R-t))
    (fun x hx => (smoothConeCutoff_uniform_support δ R t t t x₀ x ⟨le_rfl,le_rfl⟩ hx).1)

theorem smoothConeCutoffTimeDerivative_hasCompactSupport (δ R t : ℝ) (x₀ : KGSpatialSpace) :
    HasCompactSupport (smoothConeCutoffTimeDerivative δ R t x₀) :=
  compactSupport_of_zero_outside_compact (isCompact_closedBall x₀ (R-t))
    (fun x hx => (smoothConeCutoff_uniform_support δ R t t t x₀ x ⟨le_rfl,le_rfl⟩ hx).2.1)

theorem smoothConeCutoff_joint_contDiff
    (δ R : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    ContDiff ℝ 2 (fun z : ℝ × KGSpatialSpace => smoothConeCutoff δ R z.1 x₀ z.2) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_fst).sub
      ((regularizedSpatialDistance_contDiff δ x₀ hδ).comp contDiff_snd))

theorem smoothConeCutoffTimeDerivative_joint_continuous
    (δ R : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    Continuous (fun z : ℝ × KGSpatialSpace => smoothConeCutoffTimeDerivative δ R z.1 x₀ z.2) := by
  have he : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  exact (he.comp ((continuous_const.sub continuous_fst).sub
    ((regularizedSpatialDistance_contDiff δ x₀ hδ).continuous.comp continuous_snd))).neg

theorem regularizedDistanceGradient_continuous
    (δ : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    Continuous (regularizedDistanceGradient δ x₀) := by
  exact ((regularizedSpatialDistance_contDiff δ x₀ hδ).continuous.inv₀
    (fun x => ne_of_gt (regularizedSpatialDistance_pos δ x₀ x hδ))).smul
      (continuous_id.sub continuous_const)

theorem smoothConeCutoffGradient_joint_continuous
    (δ R : ℝ) (x₀ : KGSpatialSpace) (hδ : 0 < δ) :
    Continuous (fun z : ℝ × KGSpatialSpace => smoothConeCutoffGradient δ R z.1 x₀ z.2) :=
  (smoothConeCutoffTimeDerivative_joint_continuous δ R x₀ hδ).smul
    ((regularizedDistanceGradient_continuous δ x₀ hδ).comp continuous_snd)

end AASCKleinGordon
