import EHKGAffineDiamondUniqueness

/-! Quantitative containment and genuinely shifted inhabited continuation
domains. No assumption that a noncentral leaf is Cauchy on the whole old diamond. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem time_affine_time (time scale : ℝ) (p : CoordinatePoint) :
    timeAffineMap time scale p 0 = time + scale * p 0 := by
  simp [time_affine_coordinate]

theorem time_affine_space (time scale : ℝ) (p : CoordinatePoint) :
    (coordinateSpatialSplit (timeAffineMap time scale p)).2 = scale • (coordinateSpatialSplit p).2 := by
  rw [coordinate_split_space, coordinate_split_space]
  ext i
  change time * (Pi.single (0 : Fin 4) (1 : ℝ) : CoordinatePoint) i.succ + scale * p i.succ = scale * p i.succ
  simp

theorem affine_cauchy_is_slice (time scale : ℝ) (x : KGSpatialSpace) :
    affineCauchyPoint time scale x = evolutionSlicePoint time (scale • x) := by
  apply coordinateSpatialSplit.injective
  apply Prod.ext
  · change timeAffineMap time scale (centralLeafPoint x) 0 = evolutionSlicePoint time (scale • x) 0
    rw [time_affine_time, central_leaf_time, evolution_slice_time, mul_zero, add_zero]
  · rw [affineCauchyPoint, time_affine_space, central_leaf_space, evolution_slice_space]

theorem affine_diamond_contained (nu time scale : ℝ) (positive : 0 < scale)
    (margin : |time| + scale * protectedRadius nu ≤ protectedRadius nu) :
    affineDependenceDiamond nu time scale ⊆ protectedDiamond nu := by
  intro p hp
  let q := timeAffineMap (-time / scale) scale⁻¹ p
  have qInside : q ∈ protectedDiamond nu := hp
  have identity : timeAffineMap time scale q = p := time_affine_inverse_right _ _ (ne_of_gt positive) p
  rw [← identity]
  change |timeAffineMap time scale q 0| + ‖(coordinateSpatialSplit (timeAffineMap time scale q)).2‖ < protectedRadius nu
  rw [time_affine_time, time_affine_space, norm_smul, Real.norm_eq_abs, abs_of_pos positive]
  have clockBound : |time + scale * q 0| ≤ |time| + scale * |q 0| := by
    simpa only [abs_mul, abs_of_pos positive] using abs_add_le time (scale * q 0)
  have strict := mul_lt_mul_of_pos_left qInside positive
  change scale * (|q 0| + ‖(coordinateSpatialSplit q).2‖) < scale * protectedRadius nu at strict
  nlinarith

theorem affine_diamond_nonempty (nu time scale : ℝ) (nonzero : scale ≠ 0) :
    (affineDependenceDiamond nu time scale).Nonempty := by
  refine ⟨timeAffineMap time scale 0, (affine_diamond_image nu time scale nonzero 0).mpr ?_⟩
  exact protected_diamond_zero nu

theorem quarter_shifted_diamond (nu : ℝ) :
    protectedRadius nu / 4 ≠ 0 ∧
      (affineDependenceDiamond nu (protectedRadius nu / 4) (1 / 4)).Nonempty ∧
      affineDependenceDiamond nu (protectedRadius nu / 4) (1 / 4) ⊆ protectedDiamond nu := by
  have radius := protected_radius_positive nu
  refine ⟨ne_of_gt (by linarith), affine_diamond_nonempty _ _ _ (by norm_num), ?_⟩
  apply affine_diamond_contained nu _ _ (by norm_num)
  rw [abs_of_pos (show 0 < protectedRadius nu / 4 by linarith)]
  linarith

end AASCKleinGordon.CurvedKG
