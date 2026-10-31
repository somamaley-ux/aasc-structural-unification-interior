import CoordinateMetricNaturality

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

def lorentzCoordinateMap (L : LorentzComparison) (x : CoordinatePoint) : CoordinatePoint :=
  L.forward.mulVec x

def lorentzCoordinateEquiv (L : LorentzComparison) : CoordinatePoint ≃L[ℝ] CoordinatePoint where
  toFun := lorentzCoordinateMap L
  invFun := L.inverse.mulVec
  map_add' x y := by simp [lorentzCoordinateMap, Matrix.mulVec_add]
  map_smul' r x := by simp [lorentzCoordinateMap, Matrix.mulVec_smul]
  left_inv x := by
    change L.inverse.mulVec (L.forward.mulVec x) = x
    rw [Matrix.mulVec_mulVec, L.left_inverse]
    simp
  right_inv x := by
    change L.forward.mulVec (L.inverse.mulVec x) = x
    rw [Matrix.mulVec_mulVec, L.right_inverse]
    simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    simp only [lorentzCoordinateMap, Matrix.mulVec, dotProduct]
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop

theorem lorentzCoordinateMap_smooth (L : LorentzComparison) :
    ContDiff ℝ ⊤ (lorentzCoordinateMap L) := (lorentzCoordinateEquiv L).contDiff

theorem lorentzCoordinateMap_zero (L : LorentzComparison) : lorentzCoordinateMap L 0 = 0 := by
  simp [lorentzCoordinateMap]

theorem lorentzCoordinateMap_hasFDerivAt (L : LorentzComparison) (p : CoordinatePoint) :
    HasFDerivAt (lorentzCoordinateMap L) (lorentzCoordinateEquiv L).toContinuousLinearMap p :=
  (lorentzCoordinateEquiv L).toContinuousLinearMap.hasFDerivAt

theorem lorentzCoordinateMap_smoothCoordinateAt (L : LorentzComparison) (p : CoordinatePoint) :
    SmoothCoordinateAt (lorentzCoordinateMap L) p :=
  smoothCoordinateAt_of_derivative_equiv _ p (lorentzCoordinateEquiv L)
    (lorentzCoordinateMap_smooth L).contDiffAt (lorentzCoordinateMap_hasFDerivAt L p)

theorem lorentzCoordinateMap_jacobian (L : LorentzComparison) (p : CoordinatePoint) :
    coordinateJacobian (lorentzCoordinateMap L) p = L.forward := by
  ext i a
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((coordinateProjection j).hasFDerivAt (x := p)).const_mul (L.forward i j))
  have hd' : HasFDerivAt (fun x => lorentzCoordinateMap L x i)
      (∑ j : Fin 4, L.forward i j • coordinateProjection j) p := by
    simpa only [lorentzCoordinateMap, Matrix.mulVec, dotProduct, coordinateProjection,
      ContinuousLinearMap.proj_apply] using hd
  unfold coordinateJacobian
  rw [hd'.fderiv]
  simp [coordinateProjection, Pi.single_apply, ite_mul, mul_ite]

#print axioms lorentzCoordinateMap_smooth
#print axioms lorentzCoordinateMap_zero
#print axioms lorentzCoordinateMap_hasFDerivAt
#print axioms lorentzCoordinateMap_smoothCoordinateAt
#print axioms lorentzCoordinateMap_jacobian
end
end AASCSemanticExhaustion
