import SemanticResponseCoordinates
import CurvatureTransportDefinitions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
Independent algebraic fibre semantics for the source's first-curvature step.
The input is an arbitrary function on tensors satisfying the original curvature
laws. Affinity, symmetry and covariance are stated as functional laws, not as
a Ricci expression or a completeness certificate. This fibre problem still
requires a source-preserving jet/locality handoff from the original geometric
SameScopeMetric1 predicate; it does not redefine that predicate.
-/

namespace AASCSemanticExhaustion

def CurvatureAffine (E : curvatureSpace → Tensor2) : Prop :=
  (∀ R S, E (R + S) = E R + E S - E 0) ∧
  (∀ r : ℝ, ∀ R, E (r • R) = r • (E R - E 0) + E 0)

def TensorCovariant (E : curvatureSpace → Tensor2) : Prop :=
  ∀ L : LorentzComparison, ∀ R S : curvatureSpace,
    (S : Tensor4) = pullbackFour L.forward (R : Tensor4) →
      E S = L.forward.transpose * E R * L.forward

def TensorSymmetric (E : curvatureSpace → Tensor2) : Prop :=
  ∀ R i j, E R i j = E R j i

def responseLinearPart (E : curvatureSpace → Tensor2) (h : CurvatureAffine E) :
    curvatureSpace →ₗ[ℝ] Tensor2 where
  toFun R := E R - E 0
  map_add' R S := by rw [h.1 R S]; abel
  map_smul' r R := by rw [h.2 r R]; simp

theorem response_linear_decomposition (E : curvatureSpace → Tensor2)
    (h : CurvatureAffine E) (R : curvatureSpace) :
    E R = E 0 + responseLinearPart E h R := by
  change E R = E 0 + (E R - E 0)
  abel

theorem pullbackFour_zero (L : Tensor2) : pullbackFour L (0 : Tensor4) = 0 := by
  funext a b c d
  simp [pullbackFour]

/-- The metric-baseline conclusion is derived from the arbitrary response's
original covariance law, not supplied as an invariant-baseline field. -/
theorem covariance_forces_unique_metric_baseline
    (E : curvatureSpace → Tensor2) (h : TensorCovariant E) :
    ∃! c : ℝ, E 0 = c • metric := by
  have invariant : InvariantBaseline (E 0) := by
    intro L
    have hz : ((0 : curvatureSpace) : Tensor4) =
        pullbackFour L.forward ((0 : curvatureSpace) : Tensor4) :=
      (pullbackFour_zero L.forward).symm
    exact (h L 0 0 hz).symm
  exact invariant_baseline_unique_metric_multiple (E 0) invariant

theorem response_linearPart_symmetric
    (E : curvatureSpace → Tensor2) (h : CurvatureAffine E)
    (symmetric : TensorSymmetric E) :
    TensorSymmetric (responseLinearPart E h) := by
  intro R i j
  change E R i j - E 0 i j = E R j i - E 0 j i
  rw [symmetric R i j, symmetric 0 i j]

theorem response_linearPart_covariant
    (E : curvatureSpace → Tensor2) (h : CurvatureAffine E)
    (covariant : TensorCovariant E) :
    TensorCovariant (responseLinearPart E h) := by
  intro L R S hS
  change E S - E 0 = L.forward.transpose * (E R - E 0) * L.forward
  rw [mul_sub, sub_mul]
  have hz : ((0 : curvatureSpace) : Tensor4) =
      pullbackFour L.forward ((0 : curvatureSpace) : Tensor4) :=
    (pullbackFour_zero L.forward).symm
  rw [← covariant L R S hS, ← covariant L 0 0 hz]

/-- A semantic reduction to the remaining linear equivariant-operator problem.
No normal form for that operator is assumed or concluded here. -/
theorem semantic_first_response_reduction
    (E : curvatureSpace → Tensor2) (affine : CurvatureAffine E)
    (symmetric : TensorSymmetric E) (covariant : TensorCovariant E) :
    ∃ c : ℝ, ∃ A : curvatureSpace →ₗ[ℝ] Tensor2,
      (∀ R, E R = c • metric + A R) ∧
      TensorSymmetric A ∧ TensorCovariant A := by
  obtain ⟨c, hc, _⟩ := covariance_forces_unique_metric_baseline E covariant
  refine ⟨c, responseLinearPart E affine, ?_,
    response_linearPart_symmetric E affine symmetric,
    response_linearPart_covariant E affine covariant⟩
  intro R
  rw [← hc]
  exact response_linear_decomposition E affine R

#print axioms response_linear_decomposition
#print axioms pullbackFour_zero
#print axioms covariance_forces_unique_metric_baseline
#print axioms response_linearPart_symmetric
#print axioms response_linearPart_covariant
#print axioms semantic_first_response_reduction

end AASCSemanticExhaustion
