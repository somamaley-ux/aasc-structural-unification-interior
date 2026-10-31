import OriginalCoordinateCurvatureIdentification

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0
set_option autoImplicit false

theorem pullbackFour_neg (A : Tensor2) (R : Tensor4) : pullbackFour A (-R) = -pullbackFour A R := by
  funext a b c d
  simp [pullbackFour, mul_neg, Finset.sum_neg_distrib]

theorem pullbackFour_last_swap (A : Tensor2) (R : Tensor4) :
    pullbackFour A (fun a b c d => R a b d c) = (fun a b c d => pullbackFour A R a b d c) := by
  funext a b c d
  simp only [pullbackFour_flat]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem sum_four_pair_swap (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc
    _ = ∑ i, ∑ k, ∑ l, ∑ j, f i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      exact (sum_three_rotate (fun j k l => f i j k l)).trans
        (sum_three_rotate (fun l j k => f i j k l))
    _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

theorem pullbackFour_pair_swap (A : Tensor2) (R : Tensor4) :
    pullbackFour A (fun a b c d => R c d a b) = (fun a b c d => pullbackFour A R c d a b) := by
  funext a b c d
  simp only [pullbackFour_flat]
  rw [sum_four_pair_swap]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pullbackFour_cycle_twice (A : Tensor2) (R : Tensor4) :
    pullbackFour A (fun a b c d => R a c d b) = (fun a b c d => pullbackFour A R a c d b) := by
  rw [pullbackFour_cycle A (fun a b c d => R a d b c), pullbackFour_cycle A R]

theorem pullbackFour_preserves_curvature_laws (A : Tensor2) (R : curvatureSpace) :
    pullbackFour A R ∈ curvatureSpace := by
  have hfirst : (fun a b c d => (R : Tensor4) b a c d) = -(R : Tensor4) := by
    funext a b c d
    exact R.property.1 b a c d
  have hlast : (fun a b c d => (R : Tensor4) a b d c) = -(R : Tensor4) := by
    funext a b c d
    exact R.property.2.1 a b d c
  have hpair : (fun a b c d => (R : Tensor4) c d a b) = (R : Tensor4) := by
    funext a b c d
    exact R.property.2.2.1 c d a b
  have hcyclic : ((R : Tensor4) + (fun a b c d => (R : Tensor4) a d b c)) +
      (fun a b c d => (R : Tensor4) a c d b) = 0 := by
    funext a b c d
    change (R : Tensor4) a b c d + (R : Tensor4) a d b c + (R : Tensor4) a c d b = 0
    linarith [R.property.2.2.2 a b c d]
  have hf := congrArg (pullbackFour A) hfirst
  have hl := congrArg (pullbackFour A) hlast
  have hp := congrArg (pullbackFour A) hpair
  have hb := congrArg (pullbackFour A) hcyclic
  rw [pullbackFour_first_swap, pullbackFour_neg] at hf
  rw [pullbackFour_last_swap, pullbackFour_neg] at hl
  rw [pullbackFour_pair_swap] at hp
  rw [pullbackFour_add A ((R : Tensor4) + (fun a b c d => (R : Tensor4) a d b c))
      (fun a b c d => (R : Tensor4) a c d b),
    pullbackFour_add A (R : Tensor4) (fun a b c d => (R : Tensor4) a d b c),
    pullbackFour_cycle A (R : Tensor4), pullbackFour_cycle_twice A (R : Tensor4), pullbackFour_zero] at hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    have h := congrArg (fun T : Tensor4 => T a b c d) hf
    change pullbackFour A R b a c d = -pullbackFour A R a b c d at h
    linarith
  · intro a b c d
    have h := congrArg (fun T : Tensor4 => T a b c d) hl
    change pullbackFour A R a b d c = -pullbackFour A R a b c d at h
    linarith
  · intro a b c d
    exact (congrArg (fun T : Tensor4 => T a b c d) hp).symm
  · intro a b c d
    have h := congrArg (fun T : Tensor4 => T a b c d) hb
    change pullbackFour A R a b c d + pullbackFour A R a d b c + pullbackFour A R a c d b = 0 at h
    linarith

def curvaturePullback (A : Tensor2) (R : curvatureSpace) : curvatureSpace :=
  ⟨pullbackFour A R, pullbackFour_preserves_curvature_laws A R⟩

#print axioms pullbackFour_neg
#print axioms pullbackFour_last_swap
#print axioms sum_four_pair_swap
#print axioms pullbackFour_pair_swap
#print axioms pullbackFour_cycle_twice
#print axioms pullbackFour_preserves_curvature_laws
end
end AASCSemanticExhaustion
