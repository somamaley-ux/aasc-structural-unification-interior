import OriginalEHEulerResponse
import WickLorentzSchurSignature
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Construct a normalized frame from the actual completion of squares.
No frame/signature persistence certificate or desired response law is input. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCKleinGordon
open scoped BigOperators Topology MatrixOrder

theorem eh_positive_spatial_factor (A : Matrix (Fin 3) (Fin 3) ℝ)
    (symmetric : ∀ i j, A i j = A j i)
    (positive : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < wickMatrixQuadratic A x) :
    ∃ C : Matrix (Fin 3) (Fin 3) ℝ, IsUnit C.det ∧ A = C.transpose * C := by
  have hA : A.PosDef := by
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · ext i j
      exact symmetric j i
    · intro x hx
      simpa only [wickMatrixQuadratic, dotProduct, Matrix.mulVec,
        Finset.mul_sum, mul_assoc, star_trivial] using positive x hx
  have strict := Matrix.isStrictlyPositive_iff_posDef.mpr hA
  obtain ⟨C,hC,equal⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp strict
  refine ⟨C, (Matrix.isUnit_iff_isUnit_det C).mp hC, ?_⟩
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using equal

end
end AASCSemanticExhaustion
