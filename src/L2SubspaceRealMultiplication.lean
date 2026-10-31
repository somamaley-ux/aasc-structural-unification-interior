import HilbertBoundedPair
import L2GraphCoefficientAlgebra
import L2RealMultiplicationClosed

noncomputable section
open MeasureTheory Filter
namespace AASCKleinGordon.Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (v : X → ℝ) (hv : Measurable v) (S : Submodule ℂ (H μ)) [CompleteSpace S]
variable (hA : ∀ f : S,graphBoundedA v hv f.val ∈ S)
variable (hB : ∀ f : S,graphBoundedB v hv f.val ∈ S)

def subspaceBoundedA : S →L[ℂ] S :=
  ((graphBoundedA v hv).comp S.subtypeL).codRestrict S hA

def subspaceBoundedB : S →L[ℂ] S :=
  ((graphBoundedB v hv).comp S.subtypeL).codRestrict S hB

theorem subspaceBoundedB_injective : Function.Injective (subspaceBoundedB v hv S hB) := by
  intro f g h
  apply Subtype.ext
  apply boundedMul_injective _ (graphCoefficientB_measurable v hv).aestronglyMeasurable 1
    (Eventually.of_forall (fun x => graphCoefficientB_bound (v x)))
    (Eventually.of_forall (fun x => graphCoefficientB_ne_zero (v x)))
  exact congrArg Subtype.val h

theorem subspaceBounded_commute :
    (subspaceBoundedB v hv S hB).comp (subspaceBoundedA v hv S hA)=
      (subspaceBoundedA v hv S hA).comp (subspaceBoundedB v hv S hB) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun C : H μ →L[ℂ] H μ => C f.val) (graphBounded_commute v hv)

theorem subspaceBounded_normalized :
    (subspaceBoundedA v hv S hA).comp (subspaceBoundedA v hv S hA)+
      (subspaceBoundedB v hv S hB).comp (subspaceBoundedB v hv S hB)=ContinuousLinearMap.id ℂ S := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun C : H μ →L[ℂ] H μ => C f.val) (graphBounded_normalized v hv)

theorem subspaceBoundedA_symmetric (f g : S) :
    inner ℂ (subspaceBoundedA v hv S hA f) g=inner ℂ f (subspaceBoundedA v hv S hA g) := by
  change inner ℂ (graphBoundedA v hv f.val) g.val=inner ℂ f.val (graphBoundedA v hv g.val)
  exact boundedMul_symmetric _ _ _ _
    (Eventually.of_forall (fun x => graphCoefficientA_real (v x))) _ _

theorem subspaceBoundedB_symmetric (f g : S) :
    inner ℂ (subspaceBoundedB v hv S hB f) g=inner ℂ f (subspaceBoundedB v hv S hB g) := by
  change inner ℂ (graphBoundedB v hv f.val) g.val=inner ℂ f.val (graphBoundedB v hv g.val)
  exact boundedMul_symmetric _ _ _ _
    (Eventually.of_forall (fun x => graphCoefficientB_real (v x))) _ _

def subspaceRealMultiplication : S →ₗ.[ℂ] S :=
  BoundedPair.operator (subspaceBoundedA v hv S hA) (subspaceBoundedB v hv S hB)
    (subspaceBoundedB_injective v hv S hB)

theorem subspaceRealMultiplication_selfAdjoint :
    IsSelfAdjoint (subspaceRealMultiplication v hv S hA hB) :=
  BoundedPair.operator_selfAdjoint _ _ _ (subspaceBounded_commute v hv S hA hB)
    (subspaceBounded_normalized v hv S hA hB)
    (subspaceBoundedB_symmetric v hv S hB) (subspaceBoundedA_symmetric v hv S hA)

theorem subspaceRealMultiplication_closed :
    (subspaceRealMultiplication v hv S hA hB).IsClosed := BoundedPair.operator_closed _ _ _

theorem subspaceRealMultiplication_dense :
    Dense ((subspaceRealMultiplication v hv S hA hB).domain : Set S) :=
  BoundedPair.operator_dense _ _ _ (subspaceBounded_commute v hv S hA hB)
    (subspaceBoundedB_symmetric v hv S hB)

theorem subspaceRealMultiplication_mem_graph (f g : S) :
    (f,g) ∈ (subspaceRealMultiplication v hv S hA hB).graph ↔
      g.val=ᵐ[μ] (fun x => (v x : ℂ)*f.val x) := by
  rw [subspaceRealMultiplication,BoundedPair.operator_graph,BoundedPair.mem_relation]
  have hval : subspaceBoundedB v hv S hB g=subspaceBoundedA v hv S hA f ↔
      graphBoundedB v hv g.val=graphBoundedA v hv f.val := Subtype.ext_iff
  rw [hval]
  change graphBoundedB v hv g.val=graphBoundedA v hv f.val ↔
    (f.val,g.val) ∈ realMultiplicationGraph v
  rw [realMultiplicationGraph_eq_kernel v hv]
  change graphBoundedB v hv g.val=graphBoundedA v hv f.val ↔
    graphBoundedB v hv g.val-graphBoundedA v hv f.val=0
  exact sub_eq_zero.symm

end AASCKleinGordon.Multiplication
