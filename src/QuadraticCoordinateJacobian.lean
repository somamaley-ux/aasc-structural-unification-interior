import QuadraticCoordinateMaps

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def coordinateFrameMatrix (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) : Tensor2 :=
  fun i a => B (Pi.single a 1) i

def quadraticJacobianDerivative (Q : CoordinateQuadraticArray) (i a : Fin 4) :
    CoordinatePoint →L[ℝ] ℝ := ∑ c : Fin 4, Q i a c • coordinateProjection c

theorem quadraticCoordinateMap_jacobian_zero (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) :
    coordinateJacobian (quadraticCoordinateMap p B Q) 0 = coordinateFrameMatrix B := by
  ext i a
  rw [quadraticCoordinateMap_jacobian p B Q symmetric]
  simp [coordinateFrameMatrix]

theorem quadraticJacobian_hasFDerivAt (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) (x : CoordinatePoint) (i a : Fin 4) :
    HasFDerivAt (fun y => coordinateJacobian (quadraticCoordinateMap p B Q) y i a)
      (quadraticJacobianDerivative Q i a) x := by
  have heq : (fun y => coordinateJacobian (quadraticCoordinateMap p B Q) y i a) =
      (fun y => B (Pi.single a 1) i + ∑ c : Fin 4, Q i a c * y c) :=
    funext (fun y => quadraticCoordinateMap_jacobian p B Q symmetric y i a)
  rw [heq]
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun c _ =>
    ((coordinateProjection c).hasFDerivAt (x := x)).const_mul (Q i a c))
  simpa only [quadraticJacobianDerivative, zero_add, Pi.add_apply, coordinateProjection,
    ContinuousLinearMap.proj_apply] using (hasFDerivAt_const (B (Pi.single a 1) i) x).add hs

theorem quadraticJacobianDerivative_basis (Q : CoordinateQuadraticArray) (i a c : Fin 4) :
    quadraticJacobianDerivative Q i a (Pi.single c 1) = Q i a c := by
  simp [quadraticJacobianDerivative, coordinateProjection, Pi.single_apply, mul_ite]

theorem coordinateFrameMatrix_refl :
    coordinateFrameMatrix (ContinuousLinearEquiv.refl ℝ CoordinatePoint) = 1 := by
  ext i a
  simp [coordinateFrameMatrix, Pi.single_apply, Matrix.one_apply, eq_comm]

#print axioms quadraticCoordinateMap_jacobian_zero
#print axioms quadraticJacobian_hasFDerivAt
#print axioms quadraticJacobianDerivative_basis
#print axioms coordinateFrameMatrix_refl
end
end AASCSemanticExhaustion
