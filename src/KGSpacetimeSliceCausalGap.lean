import KGSpacetimeSpatialSlices
import KGConcreteSineSecondDerivatives
import KGCommutatorCorrelationSupport
import Mathlib.Topology.Order.Compact

noncomputable section
set_option maxHeartbeats 1400000
open Set
open scoped SchwartzMap
namespace AASCKleinGordon

def spacetimeCausalGap (z : Spacetime) : ℝ :=
  ‖(spacetimeSpatialJoin.symm z).2‖-|(spacetimeSpatialJoin.symm z).1|

theorem spacetimeCausalGap_continuous : Continuous spacetimeCausalGap :=
  (continuous_snd.comp spacetimeSpatialJoin.symm.continuous).norm.sub
    (continuous_fst.comp spacetimeSpatialJoin.symm.continuous).abs

theorem spacetimeCausalGap_join (t : ℝ) (x : KGSpatialSpace) :
    spacetimeCausalGap (spacetimeSpatialJoin (t,x))=‖x‖-|t| := by
  simp [spacetimeCausalGap]

theorem spacetimeMinkowskiSquare_join (t : ℝ) (x : KGSpatialSpace) :
    spacetimeMinkowskiSquare (spacetimeSpatialJoin (t,x))=‖x‖^2-t^2 := by
  have hn : ‖x‖^2=x 0^2+x 1^2+x 2^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]
    <;> ring
  unfold spacetimeMinkowskiSquare minkowskiDot
  dsimp only
  have h1 : spacetimeSpatialJoin (t,x) (1 : Fin 4)=x (0 : Fin 3) := rfl
  have h2 : spacetimeSpatialJoin (t,x) (2 : Fin 4)=x (1 : Fin 3) := rfl
  have h3 : spacetimeSpatialJoin (t,x) (3 : Fin 4)=x (2 : Fin 3) := rfl
  rw [spacetimeSpatialJoin_zero,h1,h2,h3,hn]
  ring

theorem spacetimeCausalGap_pos_of_outside (z : Spacetime) (hz : z ∉ closedCausalCone) :
    0 < spacetimeCausalGap z := by
  obtain ⟨⟨t,x⟩,hjoin⟩ := spacetimeSpatialJoin.surjective z
  subst z
  have hs : 0 < spacetimeMinkowskiSquare (spacetimeSpatialJoin (t,x)) := lt_of_not_ge hz
  rw [spacetimeMinkowskiSquare_join] at hs
  rw [spacetimeCausalGap_join]
  nlinarith [sq_abs t,norm_nonneg x,abs_nonneg t]

/-- Compact spacetime support disjoint from the original closed causal cone gives
the strict Euclidean spatial slack needed by the proved sine finite-propagation theorem. -/
theorem spacetimeSpatialSlice_vanishes_on_larger_ball
    (h : 𝓢(Spacetime,ℂ)) (hc : HasCompactSupport (h : Spacetime → ℂ))
    (hs : Disjoint (tsupport (h : Spacetime → ℂ)) closedCausalCone) (t : ℝ) :
    ∃ R : ℝ, |t| < R ∧ ∀ x ∈ Metric.closedBall (0 : KGSpatialSpace) R,
      spacetimeSpatialSliceCLM t h x=0 := by
  by_cases hne : (tsupport (h : Spacetime → ℂ)).Nonempty
  · obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn hne spacetimeCausalGap_continuous.continuousOn
    have hgap : 0 < spacetimeCausalGap z :=
      spacetimeCausalGap_pos_of_outside z (fun hzc => Set.disjoint_left.mp hs hz hzc)
    refine ⟨|t|+spacetimeCausalGap z/2,by linarith,?_⟩
    intro x hx
    by_contra hx0
    have hxmem : spacetimeSpatialJoin (t,x) ∈ tsupport (h : Spacetime → ℂ) :=
      subset_tsupport _ hx0
    have hb := hmin hxmem
    change spacetimeCausalGap z ≤ spacetimeCausalGap (spacetimeSpatialJoin (t,x)) at hb
    rw [spacetimeCausalGap_join] at hb
    have hn : ‖x‖ ≤ |t|+spacetimeCausalGap z/2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    linarith
  · refine ⟨|t|+1,by linarith,?_⟩
    intro x hx
    by_contra hx0
    exact hne ⟨spacetimeSpatialJoin (t,x),subset_tsupport _ hx0⟩

theorem spatialSineSlice_origin_zero_off_causal_cone
    (a : Parameters) (h : 𝓢(Spacetime,ℂ)) (hc : HasCompactSupport (h : Spacetime → ℂ))
    (hs : Disjoint (tsupport (h : Spacetime → ℂ)) closedCausalCone) (t : ℝ) :
    spatialSineSolutionCLM a t (spacetimeSpatialSliceCLM t h) 0=0 := by
  obtain ⟨R,hRt,hf⟩ := spacetimeSpatialSlice_vanishes_on_larger_ball h hc hs t
  exact spatialSineSolution_vanishes_of_abs_time_lt a (spacetimeSpatialSliceCLM t h) R t 0 hRt hf

end AASCKleinGordon
