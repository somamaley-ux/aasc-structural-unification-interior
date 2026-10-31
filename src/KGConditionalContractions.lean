import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

/-! Actual bounded conditional contractions on the algebraic tensor carrier.
No completion, decomposition selection, or restriction to product vectors. -/
noncomputable section
namespace AASCKleinGordon.KGQuantum
open scoped TensorProduct
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def kgRightContractionLM (y : F) : E ⊗[ℂ] F →ₗ[ℂ] E :=
  (TensorProduct.rid ℂ E).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) (innerSL ℂ y).toLinearMap)

@[simp] theorem kg_right_contraction_tmul (y : F) (x : E) (v : F) :
    kgRightContractionLM y (x ⊗ₜ[ℂ] v) = inner ℂ y v • x := by
  simp [kgRightContractionLM]

theorem kg_right_contraction_inner (y : F) (z : E ⊗[ℂ] F) (x : E) :
    inner ℂ x (kgRightContractionLM y z) = inner ℂ (x ⊗ₜ[ℂ] y) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [TensorProduct.inner_tmul,inner_smul_right,mul_comm]
  | add u v hu hv => simp only [map_add,inner_add_right,hu,hv]

theorem kg_right_contraction_bound (y : F) (z : E ⊗[ℂ] F) :
    ‖kgRightContractionLM y z‖ ≤ ‖y‖ * ‖z‖ := by
  by_cases hz : kgRightContractionLM y z=0
  · simp only [hz,norm_zero];exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have hp : 0 < ‖kgRightContractionLM y z‖ := norm_pos_iff.mpr hz
    have bound : ‖kgRightContractionLM y z‖ * ‖kgRightContractionLM y z‖ ≤
        ‖kgRightContractionLM y z‖ * (‖y‖ * ‖z‖) := by
      calc
        ‖kgRightContractionLM y z‖ * ‖kgRightContractionLM y z‖ =
            (inner ℂ (kgRightContractionLM y z) (kgRightContractionLM y z)).re :=
          (inner_self_eq_norm_mul_norm (𝕜 := ℂ) (kgRightContractionLM y z)).symm
        _ = (inner ℂ ((kgRightContractionLM y z) ⊗ₜ[ℂ] y) z).re :=
          congrArg Complex.re (kg_right_contraction_inner y z (kgRightContractionLM y z))
        _ ≤ ‖(kgRightContractionLM y z) ⊗ₜ[ℂ] y‖ * ‖z‖ :=
          re_inner_le_norm (𝕜 := ℂ) ((kgRightContractionLM y z) ⊗ₜ[ℂ] y) z
        _ = ‖kgRightContractionLM y z‖ * (‖y‖ * ‖z‖) := by
          rw [TensorProduct.norm_tmul,mul_assoc]
    by_contra h
    exact (not_lt_of_ge bound)
      (mul_lt_mul_of_pos_left (lt_of_not_ge h) hp)

def kgRightContraction (y : F) : E ⊗[ℂ] F →L[ℂ] E :=
  (kgRightContractionLM y).mkContinuous ‖y‖ (kg_right_contraction_bound y)

@[simp] theorem kg_right_contraction_apply (y : F) (z : E ⊗[ℂ] F) :
    kgRightContraction y z=kgRightContractionLM y z := rfl

def kgLeftContraction (x : E) : E ⊗[ℂ] F →L[ℂ] F :=
  (kgRightContraction x).comp
    (TensorProduct.commIsometry ℂ E F).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem kg_left_contraction_tmul (x u : E) (v : F) :
    kgLeftContraction x (u ⊗ₜ[ℂ] v) = inner ℂ x u • v := by
  simp [kgLeftContraction]

end AASCKleinGordon.KGQuantum
