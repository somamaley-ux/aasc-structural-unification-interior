import RegularLorentzResponseCore
import CubicMetricGradientWitness

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Filter
open scoped Topology BigOperators

def diagonalCoordinateEquiv (w : Fin 4 → ℝ) (hw : ∀ i, w i≠0) :
    CoordinatePoint ≃L[ℝ] CoordinatePoint where
  toLinearEquiv := {
    toFun := fun x i => w i*x i
    invFun := fun x i => (w i)⁻¹*x i
    left_inv := by intro x; ext i; simp [hw i]
    right_inv := by intro x; ext i; simp [hw i]
    map_add' := by intro x y; ext i; simp [mul_add]
    map_smul' := by intro r x; ext i; simp; ring }
  continuous_toFun := by apply continuous_pi; intro i; fun_prop
  continuous_invFun := by apply continuous_pi; intro i; fun_prop

theorem diagonalCoordinateEquiv_frame_matrix (w : Fin 4 → ℝ) (hw : ∀ i, w i≠0) :
    coordinateFrameMatrix (diagonalCoordinateEquiv w hw)=Matrix.diagonal w := by
  ext i j
  simp [coordinateFrameMatrix,diagonalCoordinateEquiv,Pi.single_apply,Matrix.diagonal_apply]

theorem cubic_witness_metric_diagonal (p : CoordinatePoint) :
    cubicMetricField scalarGradientWitnessJet p =
      Matrix.diagonal (fun i : Fin 4 => if i=0 then -1 else if i=1 then 1+(p 0)^3 else 1) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [cubicMetricField,cubicPolynomial,scalarGradientWitnessJet,metric,
      Matrix.diagonal_apply,Fin.sum_univ_four] <;>
      (try simp only [Fin.ext_iff]) <;> norm_num <;> ring

theorem cubic_witness_lorentz_frame (p : CoordinatePoint) (positive : 0<1+(p 0)^3) :
    ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
      LorentzFrameAt (cubicMetricField scalarGradientWitnessJet) p B := by
  let w : Fin 4 → ℝ := fun i => if i=1 then (Real.sqrt (1+(p 0)^3))⁻¹ else 1
  have hw : ∀ i, w i≠0 := by
    intro i
    dsimp [w]
    split_ifs
    · exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 positive))
    · norm_num
  refine ⟨diagonalCoordinateEquiv w hw,?_⟩
  change (coordinateFrameMatrix _).transpose * cubicMetricField scalarGradientWitnessJet p * coordinateFrameMatrix _=metric
  rw [diagonalCoordinateEquiv_frame_matrix,cubic_witness_metric_diagonal,Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  have hs := Real.sq_sqrt (le_of_lt positive)
  have hn : Real.sqrt (1+(p 0)^3)≠0 := ne_of_gt (Real.sqrt_pos.2 positive)
  ext a b
  fin_cases a <;> fin_cases b <;> simp [w,metric,Matrix.diagonal_apply]
  field_simp
  nlinarith

theorem cubic_witness_lorentz_frames_near_zero :
    ∀ᶠ p in 𝓝 (0:CoordinatePoint), ∃ B : CoordinatePoint ≃L[ℝ] CoordinatePoint,
      LorentzFrameAt (cubicMetricField scalarGradientWitnessJet) p B := by
  have hc : ContinuousAt (fun p : CoordinatePoint => 1+(p 0)^3) 0 :=
    continuousAt_const.add ((continuous_apply (0:Fin 4)).continuousAt.pow 3)
  have hp : 0<1+((0:CoordinatePoint) 0)^3 := by norm_num
  filter_upwards [hc.eventually (eventually_gt_nhds hp)] with p h
  exact cubic_witness_lorentz_frame p h

#print axioms diagonalCoordinateEquiv_frame_matrix
#print axioms cubic_witness_metric_diagonal
#print axioms cubic_witness_lorentz_frame
#print axioms cubic_witness_lorentz_frames_near_zero
end
end AASCSemanticExhaustion

