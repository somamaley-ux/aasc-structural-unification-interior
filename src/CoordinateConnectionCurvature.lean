import CoordinateCovariantDerivative

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def coordinateBasisField (b : Fin 4) : CoordinateVectorField := fun _ => Pi.single b 1

def connectionCurvature (Γ : ConnectionCoefficients) (x : CoordinatePoint)
    (a b c d : Fin 4) : ℝ :=
  fderiv ℝ (fun y => Γ y a d b) x (Pi.single c 1) -
    fderiv ℝ (fun y => Γ y a c b) x (Pi.single d 1) +
    (∑ e : Fin 4, Γ x a c e * Γ x e d b) - (∑ e : Fin 4, Γ x a d e * Γ x e c b)

def loweredConnectionCurvature (g : MetricField) (Γ : ConnectionCoefficients)
    (x : CoordinatePoint) (a b c d : Fin 4) : ℝ :=
  ∑ e : Fin 4, g x a e * connectionCurvature Γ x e b c d

theorem covariant_derivative_coordinate_basis (Γ : ConnectionCoefficients)
    (b c : Fin 4) :
    coordinateCovariantDerivative Γ (coordinateBasisField b) (coordinateBasisField c) =
      (fun x a => Γ x a b c) := by
  funext x a
  simp [coordinateCovariantDerivative, coordinateBasisField, Pi.single_apply,
    ite_mul, mul_ite]

theorem coordinate_basis_lie_bracket (c d : Fin 4) :
    coordinateLieBracket (coordinateBasisField c) (coordinateBasisField d) = 0 := by
  funext x a
  simp [coordinateLieBracket, coordinateBasisField]

/-- The coefficient formula is derived from the actual connection commutator
on the coordinate basis, rather than postulated as the realized curvature. -/
theorem connection_curvature_is_covariant_commutator (Γ : ConnectionCoefficients)
    (x : CoordinatePoint) (a b c d : Fin 4) :
    coordinateCovariantDerivative Γ (coordinateBasisField c)
        (coordinateCovariantDerivative Γ (coordinateBasisField d) (coordinateBasisField b)) x a -
      coordinateCovariantDerivative Γ (coordinateBasisField d)
        (coordinateCovariantDerivative Γ (coordinateBasisField c) (coordinateBasisField b)) x a =
      connectionCurvature Γ x a b c d := by
  rw [covariant_derivative_coordinate_basis, covariant_derivative_coordinate_basis]
  simp [coordinateCovariantDerivative, coordinateBasisField, connectionCurvature,
    Pi.single_apply, ite_mul, mul_ite]
  ring

#print axioms covariant_derivative_coordinate_basis
#print axioms coordinate_basis_lie_bracket
#print axioms connection_curvature_is_covariant_commutator
end
end AASCSemanticExhaustion
