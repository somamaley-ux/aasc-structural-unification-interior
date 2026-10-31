import CurvatureTransportDefinitions
import MetricHessianSpace

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem pullbackFour_flat (L : Tensor2) (R : Tensor4) (a b c d : Fin 4) :
    pullbackFour L R a b c d = ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      L i a * L j b * L k c * L l d * R i j k l := by
  simp only [pullbackFour, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pullbackFour_add (L : Tensor2) (R S : Tensor4) :
    pullbackFour L (R + S) = pullbackFour L R + pullbackFour L S := by
  funext a b c d
  simp [pullbackFour, mul_add, Finset.sum_add_distrib]

theorem pullbackFour_smul (L : Tensor2) (r : ℝ) (R : Tensor4) :
    pullbackFour L (r • R) = r • pullbackFour L R := by
  funext a b c d
  simp only [pullbackFour_flat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pullbackFour_middle (L : Tensor2) (R : Tensor4) :
    pullbackFour L (fun a b c d => R a c b d) =
      (fun a b c d => pullbackFour L R a c b d) := by
  funext a b c d
  simp only [pullbackFour_flat]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem sum_three_rotate (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ i, ∑ j, f i j k := by
  calc
    _ = ∑ i, ∑ k, ∑ j, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem pullbackFour_cycle (L : Tensor2) (R : Tensor4) :
    pullbackFour L (fun a b c d => R a d b c) =
      (fun a b c d => pullbackFour L R a d b c) := by
  funext a b c d
  simp only [pullbackFour_flat]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem normalJet_frame_natural (L : Tensor2) (R S : curvatureSpace)
    (hS : (S : Tensor4) = pullbackFour L R) :
    ((normalJetMap S : metricHessianSpace) : Tensor4) =
      pullbackFour L ((normalJetMap R : metricHessianSpace) : Tensor4) := by
  have hn : ((normalJetMap R : metricHessianSpace) : Tensor4) =
      (-(1 / 3 : ℝ)) • ((fun a b c d => (R : Tensor4) a c b d) +
        (fun a b c d => (R : Tensor4) a d b c)) := rfl
  rw [hn, pullbackFour_smul, pullbackFour_add,
    pullbackFour_middle L (R : Tensor4), pullbackFour_cycle L (R : Tensor4)]
  funext a b c d
  change -(1 / 3 : ℝ) * ((S : Tensor4) a c b d + (S : Tensor4) a d b c) = _
  rw [hS]
  rfl

#print axioms pullbackFour_flat
#print axioms pullbackFour_add
#print axioms pullbackFour_smul
#print axioms pullbackFour_middle
#print axioms sum_three_rotate
#print axioms pullbackFour_cycle
#print axioms normalJet_frame_natural
end
end AASCSemanticExhaustion
