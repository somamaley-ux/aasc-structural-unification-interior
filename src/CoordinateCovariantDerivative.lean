import CoordinateLeviCivitaUniqueness

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

abbrev CoordinateVectorField := CoordinatePoint → CoordinatePoint

def coordinateCovariantDerivative (Γ : ConnectionCoefficients)
    (X Y : CoordinateVectorField) (x : CoordinatePoint) (a : Fin 4) : ℝ :=
  fderiv ℝ (fun y => Y y a) x (X x) +
    ∑ b : Fin 4, ∑ c : Fin 4, Γ x a b c * X x b * Y x c

def coordinateLieBracket (X Y : CoordinateVectorField) (x : CoordinatePoint) (a : Fin 4) : ℝ :=
  fderiv ℝ (fun y => Y y a) x (X x) - fderiv ℝ (fun y => X y a) x (Y x)

theorem coordinate_covariant_add_direction (Γ : ConnectionCoefficients)
    (X Z Y : CoordinateVectorField) (x : CoordinatePoint) (a : Fin 4) :
    coordinateCovariantDerivative Γ (X + Z) Y x a =
      coordinateCovariantDerivative Γ X Y x a + coordinateCovariantDerivative Γ Z Y x a := by
  simp [coordinateCovariantDerivative, map_add, mul_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem coordinate_covariant_smul_direction (Γ : ConnectionCoefficients)
    (f : CoordinatePoint → ℝ) (X Y : CoordinateVectorField) (x : CoordinatePoint) (a : Fin 4) :
    coordinateCovariantDerivative Γ (fun y => f y • X y) Y x a =
      f x * coordinateCovariantDerivative Γ X Y x a := by
  simp only [coordinateCovariantDerivative, map_smul, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem coordinate_covariant_add_field (Γ : ConnectionCoefficients)
    (X Y Z : CoordinateVectorField) (x : CoordinatePoint) (a : Fin 4)
    (hY : DifferentiableAt ℝ (fun y => Y y a) x)
    (hZ : DifferentiableAt ℝ (fun y => Z y a) x) :
    coordinateCovariantDerivative Γ X (Y + Z) x a =
      coordinateCovariantDerivative Γ X Y x a + coordinateCovariantDerivative Γ X Z x a := by
  change (fderiv ℝ (fun y => Y y a + Z y a) x) (X x) + _ = _
  have hd := (hY.hasFDerivAt.add hZ.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => Y y a + Z y a) x = _ at hd
  rw [hd]
  simp [coordinateCovariantDerivative, mul_add, Finset.sum_add_distrib]
  ring

theorem coordinate_covariant_leibniz (Γ : ConnectionCoefficients)
    (f : CoordinatePoint → ℝ) (X Y : CoordinateVectorField) (x : CoordinatePoint) (a : Fin 4)
    (hf : DifferentiableAt ℝ f x) (hY : DifferentiableAt ℝ (fun y => Y y a) x) :
    coordinateCovariantDerivative Γ X (fun y => f y • Y y) x a =
      f x * coordinateCovariantDerivative Γ X Y x a + fderiv ℝ f x (X x) * Y x a := by
  change (fderiv ℝ (fun y => f y * Y y a) x) (X x) + _ = _
  have hd := (hf.hasFDerivAt.mul hY.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y * Y y a) x = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [coordinateCovariantDerivative, Pi.smul_apply, smul_eq_mul]
  have hsum : (∑ b : Fin 4, ∑ c : Fin 4, Γ x a b c * X x b * (f x * Y x c)) =
      ∑ b : Fin 4, ∑ c : Fin 4, f x * (Γ x a b c * X x b * Y x c) := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsum]
  simp only [mul_add, Finset.mul_sum]
  ring

theorem coordinate_covariant_torsion (Γ : ConnectionCoefficients)
    (torsion : CoordinateTorsionFree Γ) (X Y : CoordinateVectorField)
    (x : CoordinatePoint) (a : Fin 4) :
    coordinateCovariantDerivative Γ X Y x a - coordinateCovariantDerivative Γ Y X x a =
      coordinateLieBracket X Y x a := by
  have hsum : (∑ b : Fin 4, ∑ c : Fin 4, Γ x a b c * Y x b * X x c) =
      ∑ b : Fin 4, ∑ c : Fin 4, Γ x a b c * X x b * Y x c := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [torsion x a c b]
    ring
  unfold coordinateCovariantDerivative coordinateLieBracket
  rw [hsum]
  ring

#print axioms coordinate_covariant_add_direction
#print axioms coordinate_covariant_smul_direction
#print axioms coordinate_covariant_add_field
#print axioms coordinate_covariant_leibniz
#print axioms coordinate_covariant_torsion
end
end AASCSemanticExhaustion
