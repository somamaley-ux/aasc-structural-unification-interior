import NormalJetFrameNaturality

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem pullbackFour_sub (L : Tensor2) (H K : Tensor4) :
    pullbackFour L (H - K) = pullbackFour L H - pullbackFour L K := by
  funext a b c d
  simp only [pullbackFour_flat, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem pullbackFour_first_swap (L : Tensor2) (H : Tensor4) :
    pullbackFour L (fun a b c d => H b a c d) =
      (fun a b c d => pullbackFour L H b a c d) := by
  funext a b c d
  simp only [pullbackFour_flat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Curvature extraction commutes with the actual four-index linear pullback.
This does not presume that a general nonlinear chart transforms curvature. -/
theorem curvatureOfNormalHessian_pullback (L : Tensor2) (H : Tensor4) :
    curvatureOfNormalHessian (pullbackFour L H) =
      pullbackFour L (curvatureOfNormalHessian H) := by
  have hc : curvatureOfNormalHessian H = (1 / 2 : ℝ) •
      (((fun a b c d => H a d b c) + (fun a b c d => H b c a d)) -
        (fun a b c d => H a c b d) - (fun a b c d => H b d a c)) := rfl
  rw [hc, pullbackFour_smul, pullbackFour_sub, pullbackFour_sub, pullbackFour_add,
    pullbackFour_cycle L H, pullbackFour_middle L H]
  have hbc : pullbackFour L (fun a b c d => H b c a d) =
      (fun a b c d => pullbackFour L H b c a d) := by
    rw [pullbackFour_first_swap L (fun a b c d => H a c b d), pullbackFour_middle L H]
  have hbd : pullbackFour L (fun a b c d => H b d a c) =
      (fun a b c d => pullbackFour L H b d a c) := by
    rw [pullbackFour_first_swap L (fun a b c d => H a d b c), pullbackFour_cycle L H]
  rw [hbc, hbd]
  rfl

#print axioms pullbackFour_sub
#print axioms pullbackFour_first_swap
#print axioms curvatureOfNormalHessian_pullback
end
end AASCSemanticExhaustion
