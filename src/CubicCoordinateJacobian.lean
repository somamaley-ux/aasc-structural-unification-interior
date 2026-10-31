import CubicCoordinateMaps
import CoordinateLeviCivita

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def coordinateJacobian (F : CoordinatePoint → CoordinatePoint) (x : CoordinatePoint) : Tensor2 :=
  fun i a => fderiv ℝ (fun y => F y i) x (Pi.single a 1)

theorem cubic_component_hasFDerivAt (C : Tensor4) (x : CoordinatePoint) (i : Fin 4) :
    HasFDerivAt (fun y => cubicCoordinateMap C y i)
      (coordinateProjection i + cubicDerivative (C i) x) x := by
  simpa only [cubicCoordinateMap, Pi.add_apply] using
    (coordinateProjection i).hasFDerivAt.add (cubicPolynomial_hasFDerivAt (C i) x)

theorem cubic_coordinate_jacobian_formula (C : Tensor4) (laws : CubicCoordinateLaws C)
    (x : CoordinatePoint) (i a : Fin 4) :
    coordinateJacobian (cubicCoordinateMap C) x i a =
      (1 : Tensor2) i a + quadraticPolynomial (fun b c => C i a b c) x := by
  have hrow : SymmetricCubicArray (C i) := ⟨laws.1 i, laws.2 i⟩
  unfold coordinateJacobian
  rw [(cubic_component_hasFDerivAt C x i).fderiv]
  simp [coordinateProjection, symmetric_cubic_derivative_basis (C i) hrow,
    Pi.single_apply, Matrix.one_apply, eq_comm]

theorem cubic_coordinate_jacobian_zero (C : Tensor4) (laws : CubicCoordinateLaws C) :
    coordinateJacobian (cubicCoordinateMap C) 0 = 1 := by
  ext i a
  rw [cubic_coordinate_jacobian_formula C laws]
  simp [quadraticPolynomial_zero]

theorem cubic_coordinate_jacobian_hasFDerivAt (C : Tensor4) (laws : CubicCoordinateLaws C)
    (x : CoordinatePoint) (i a : Fin 4) :
    HasFDerivAt (fun y => coordinateJacobian (cubicCoordinateMap C) y i a)
      (quadraticDerivative (fun b c => C i a b c) x) x := by
  have heq : (fun y => coordinateJacobian (cubicCoordinateMap C) y i a) =
      (fun y => (1 : Tensor2) i a + quadraticPolynomial (fun b c => C i a b c) y) :=
    funext (fun y => cubic_coordinate_jacobian_formula C laws y i a)
  rw [heq]
  simpa only [zero_add, Pi.add_apply] using
    (hasFDerivAt_const ((1 : Tensor2) i a) x).add
      (quadraticPolynomial_hasFDerivAt (fun b c => C i a b c) x)

theorem cubic_coordinate_jacobian_fderiv (C : Tensor4) (laws : CubicCoordinateLaws C)
    (x : CoordinatePoint) (i a : Fin 4) :
    fderiv ℝ (fun y => coordinateJacobian (cubicCoordinateMap C) y i a) x =
      quadraticDerivative (fun b c => C i a b c) x :=
  (cubic_coordinate_jacobian_hasFDerivAt C laws x i a).fderiv

theorem cubic_coordinate_jacobian_first_zero (C : Tensor4) (laws : CubicCoordinateLaws C)
    (i a : Fin 4) :
    fderiv ℝ (fun y => coordinateJacobian (cubicCoordinateMap C) y i a) 0 = 0 := by
  rw [cubic_coordinate_jacobian_fderiv C laws, quadraticDerivative_zero]

theorem cubic_coordinate_jacobian_second (C : Tensor4) (laws : CubicCoordinateLaws C)
    (i a c d : Fin 4) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => coordinateJacobian (cubicCoordinateMap C) y i a) x
      (Pi.single c 1)) 0 (Pi.single d 1) = C i a c d := by
  simp_rw [cubic_coordinate_jacobian_fderiv C laws]
  rw [quadraticDerivative_eval_linear,
    (quadraticSecondDerivative (fun b e => C i a b e) (Pi.single c 1)).hasFDerivAt.fderiv,
    quadraticSecondDerivative_basis]
  rw [laws.2 i a d c]
  ring

#print axioms cubic_component_hasFDerivAt
#print axioms cubic_coordinate_jacobian_formula
#print axioms cubic_coordinate_jacobian_zero
#print axioms cubic_coordinate_jacobian_hasFDerivAt
#print axioms cubic_coordinate_jacobian_fderiv
#print axioms cubic_coordinate_jacobian_first_zero
#print axioms cubic_coordinate_jacobian_second
end
end AASCSemanticExhaustion
