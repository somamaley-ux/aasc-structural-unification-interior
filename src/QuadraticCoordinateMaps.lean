import QuadraticCoordinateBasis
import CoordinateMetricNaturality

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

abbrev CoordinateQuadraticArray := Fin 4 → Tensor2

def quadraticCoordinateMap (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (Q : CoordinateQuadraticArray) (x : CoordinatePoint) : CoordinatePoint :=
  fun i => p i + B x i + quadraticPolynomial (Q i) x

def quadraticCoordinateDerivative (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (Q : CoordinateQuadraticArray) (x : CoordinatePoint) : CoordinatePoint →L[ℝ] CoordinatePoint :=
  ContinuousLinearMap.pi (fun i => (coordinateProjection i).comp B.toContinuousLinearMap +
    quadraticDerivative (Q i) x)

theorem quadraticCoordinateMap_zero (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (Q : CoordinateQuadraticArray) : quadraticCoordinateMap p B Q 0 = p := by
  funext i
  simp [quadraticCoordinateMap, quadraticPolynomial_zero]

theorem quadraticCoordinateMap_smooth (p : CoordinatePoint) (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (Q : CoordinateQuadraticArray) : ContDiff ℝ ⊤ (quadraticCoordinateMap p B Q) := by
  unfold quadraticCoordinateMap quadraticPolynomial
  fun_prop

theorem quadraticCoordinateMap_component_hasFDerivAt (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray)
    (x : CoordinatePoint) (i : Fin 4) :
    HasFDerivAt (fun y => quadraticCoordinateMap p B Q y i)
      ((coordinateProjection i).comp B.toContinuousLinearMap + quadraticDerivative (Q i) x) x := by
  have hB := (coordinateProjection i).hasFDerivAt.comp x B.toContinuousLinearMap.hasFDerivAt
  have hd := ((hasFDerivAt_const (p i) x).add hB).add (quadraticPolynomial_hasFDerivAt (Q i) x)
  simpa only [quadraticCoordinateMap, zero_add, Pi.add_apply] using hd

theorem quadraticCoordinateMap_hasFDerivAt (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray) (x : CoordinatePoint) :
    HasFDerivAt (quadraticCoordinateMap p B Q) (quadraticCoordinateDerivative B Q x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact quadraticCoordinateMap_component_hasFDerivAt p B Q x i

theorem quadraticCoordinateDerivative_zero (B : CoordinatePoint ≃L[ℝ] CoordinatePoint)
    (Q : CoordinateQuadraticArray) : quadraticCoordinateDerivative B Q 0 = B.toContinuousLinearMap := by
  ext v i
  simp [quadraticCoordinateDerivative, quadraticDerivative_zero, coordinateProjection]

theorem quadraticCoordinateMap_hasFDerivAt_zero (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray) :
    HasFDerivAt (quadraticCoordinateMap p B Q) B.toContinuousLinearMap 0 := by
  simpa only [quadraticCoordinateDerivative_zero] using quadraticCoordinateMap_hasFDerivAt p B Q 0

theorem quadraticCoordinateMap_local_chart (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray) :
    SmoothCoordinateAt (quadraticCoordinateMap p B Q) 0 :=
  smoothCoordinateAt_of_derivative_equiv _ 0 B (quadraticCoordinateMap_smooth p B Q).contDiffAt
    (quadraticCoordinateMap_hasFDerivAt_zero p B Q)

theorem quadraticCoordinateMap_jacobian (p : CoordinatePoint)
    (B : CoordinatePoint ≃L[ℝ] CoordinatePoint) (Q : CoordinateQuadraticArray)
    (symmetric : ∀ i a b, Q i a b = Q i b a) (x : CoordinatePoint) (i a : Fin 4) :
    coordinateJacobian (quadraticCoordinateMap p B Q) x i a =
      B (Pi.single a 1) i + ∑ c : Fin 4, Q i a c * x c := by
  unfold coordinateJacobian
  rw [(quadraticCoordinateMap_component_hasFDerivAt p B Q x i).fderiv]
  simp [coordinateProjection, quadraticDerivative_basis (Q i) (symmetric i)]

#print axioms quadraticCoordinateMap_zero
#print axioms quadraticCoordinateMap_smooth
#print axioms quadraticCoordinateMap_component_hasFDerivAt
#print axioms quadraticCoordinateMap_hasFDerivAt
#print axioms quadraticCoordinateDerivative_zero
#print axioms quadraticCoordinateMap_hasFDerivAt_zero
#print axioms quadraticCoordinateMap_local_chart
#print axioms quadraticCoordinateMap_jacobian
end
end AASCSemanticExhaustion
