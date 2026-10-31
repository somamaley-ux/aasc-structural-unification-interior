import CubicCoordinateCalculus
import CubicJetGauge
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace AASCSemanticExhaustion
noncomputable section
set_option maxHeartbeats 0

def cubicCoordinateMap (C : Tensor4) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => x i + cubicPolynomial (C i) x

def cubicCoordinateDerivative (C : Tensor4) (x : Fin 4 → ℝ) :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi (fun i => coordinateProjection i + cubicDerivative (C i) x)

theorem cubicCoordinateMap_zero (C : Tensor4) : cubicCoordinateMap C 0 = 0 := by
  funext i
  simp [cubicCoordinateMap, cubicPolynomial_zero]

theorem cubicCoordinateMap_smooth (C : Tensor4) : ContDiff ℝ ⊤ (cubicCoordinateMap C) := by
  unfold cubicCoordinateMap cubicPolynomial
  fun_prop

theorem cubicCoordinateMap_hasFDerivAt (C : Tensor4) (x : Fin 4 → ℝ) :
    HasFDerivAt (cubicCoordinateMap C) (cubicCoordinateDerivative C x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  simpa only [cubicCoordinateMap, cubicCoordinateDerivative, ContinuousLinearMap.proj_pi,
    coordinateProjection, Pi.add_apply] using
    (coordinateProjection i).hasFDerivAt.add (cubicPolynomial_hasFDerivAt (C i) x)

theorem cubicCoordinateDerivative_zero (C : Tensor4) :
    cubicCoordinateDerivative C 0 = ContinuousLinearMap.id ℝ (Fin 4 → ℝ) := by
  ext v i
  simp [cubicCoordinateDerivative, cubicDerivative_zero, coordinateProjection]

theorem cubicCoordinateMap_hasFDerivAt_zero (C : Tensor4) :
    HasFDerivAt (cubicCoordinateMap C)
      (ContinuousLinearEquiv.refl ℝ (Fin 4 → ℝ)).toContinuousLinearMap 0 := by
  simpa only [cubicCoordinateDerivative_zero] using
    cubicCoordinateMap_hasFDerivAt C 0

def cubicCoordinateChart (C : Tensor4) : OpenPartialHomeomorph (Fin 4 → ℝ) (Fin 4 → ℝ) :=
  (cubicCoordinateMap_smooth C).contDiffAt.toOpenPartialHomeomorph (cubicCoordinateMap C)
    (f' := ContinuousLinearEquiv.refl ℝ (Fin 4 → ℝ))
    (cubicCoordinateMap_hasFDerivAt_zero C) (by simp)

theorem cubicCoordinateChart_map (C : Tensor4) :
    (cubicCoordinateChart C : (Fin 4 → ℝ) → (Fin 4 → ℝ)) = cubicCoordinateMap C := rfl

theorem cubicCoordinateChart_zero_source (C : Tensor4) :
    0 ∈ (cubicCoordinateChart C).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source (cubicCoordinateMap_smooth C).contDiffAt
    (f' := ContinuousLinearEquiv.refl ℝ (Fin 4 → ℝ))
    (cubicCoordinateMap_hasFDerivAt_zero C) (by simp)

#print axioms cubicCoordinateMap_zero
#print axioms cubicCoordinateMap_smooth
#print axioms cubicCoordinateMap_hasFDerivAt
#print axioms cubicCoordinateDerivative_zero
#print axioms cubicCoordinateMap_hasFDerivAt_zero
#print axioms cubicCoordinateChart_map
#print axioms cubicCoordinateChart_zero_source
end
end AASCSemanticExhaustion
