import QuadraticCoordinateCalculus
import Mathlib.LinearAlgebra.StdBasis

namespace AASCSemanticExhaustion
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

theorem quadraticDerivative_basis (Q : Tensor2) (symmetric : ∀ a b, Q a b = Q b a)
    (x : Fin 4 → ℝ) (a : Fin 4) :
    quadraticDerivative Q x (Pi.single a 1) = ∑ b : Fin 4, Q a b * x b := by
  have hs (i : Fin 4) : Q i a = Q a i := symmetric i a
  simp [quadraticDerivative, coordinateProjection, Pi.single_apply,
    mul_add, Finset.sum_add_distrib, mul_ite]
  simp_rw [hs]
  ring

theorem continuousLinearMap_four_coordinates {M : Type*} [AddCommGroup M] [Module ℝ M]
    (F : (Fin 4 → ℝ) →ₗ[ℝ] M) (x : Fin 4 → ℝ) :
    F x = ∑ i : Fin 4, x i • F (Pi.single i 1) := by
  have h := congrArg F ((Pi.basisFun ℝ (Fin 4)).sum_repr x)
  simpa only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr] using h.symm

#print axioms quadraticDerivative_basis
#print axioms continuousLinearMap_four_coordinates
end
end AASCSemanticExhaustion
