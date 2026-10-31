import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! A partial operator constructed as the actual closed relation B g = A f.
Self-adjointness follows from bounded symmetric A,B, injective B and AB=BA.
It is not a premise of the construction. -/
noncomputable section
namespace AASCKleinGordon.BoundedPair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def relation (A B : E →L[ℂ] E) : Submodule ℂ (E × E) :=
  (B.comp (ContinuousLinearMap.snd ℂ E E)-A.comp (ContinuousLinearMap.fst ℂ E E)).ker

theorem mem_relation (A B : E →L[ℂ] E) (f g : E) :
    (f,g) ∈ relation A B ↔ B g=A f := by
  change B g-A f=0 ↔ B g=A f
  exact sub_eq_zero

theorem relation_vertical (A B : E →L[ℂ] E) (hi : Function.Injective B) :
    ∀ z : E × E,z ∈ relation A B → z.1=0 → z.2=0 := by
  intro z hz h0
  apply hi
  have h := (mem_relation A B z.1 z.2).1 hz
  simpa only [h0,map_zero] using h

def operator (A B : E →L[ℂ] E) (hi : Function.Injective B) : E →ₗ.[ℂ] E :=
  (relation A B).toLinearPMap

theorem operator_graph (A B : E →L[ℂ] E) (hi : Function.Injective B) :
    (operator A B hi).graph=relation A B :=
  Submodule.toLinearPMap_graph_eq _ (relation_vertical A B hi)

theorem operator_closed (A B : E →L[ℂ] E) (hi : Function.Injective B) :
    (operator A B hi).IsClosed := by
  change IsClosed ((operator A B hi).graph : Set (E × E))
  rw [operator_graph]
  exact ContinuousLinearMap.isClosed_ker _

theorem symmetric_injective_dense (B : E →L[ℂ] E)
    (hs : ∀ f g,inner ℂ (B f) g=inner ℂ f (B g)) (hi : Function.Injective B) : DenseRange B := by
  have ho : (LinearMap.range B.toLinearMap)ᗮ=⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    change y=0
    apply hi
    rw [map_zero]
    apply (inner_self_eq_zero (𝕜:=ℂ)).mp
    have h := (Submodule.mem_orthogonal _ y).mp hy (B (B y)) ⟨B y,rfl⟩
    simpa only [hs] using h
  have hd := (Submodule.topologicalClosure_eq_top_iff (K:=LinearMap.range B.toLinearMap)).2 ho
  intro y
  change y ∈ (LinearMap.range B.toLinearMap).topologicalClosure
  rw [hd]
  trivial

theorem graph_on_B (A B : E →L[ℂ] E) (hi : Function.Injective B)
    (hc : B.comp A=A.comp B) (f : E) : (B f,A f) ∈ (operator A B hi).graph := by
  rw [operator_graph,mem_relation]
  exact congrArg (fun C : E →L[ℂ] E => C f) hc

theorem B_mem_domain (A B : E →L[ℂ] E) (hi : Function.Injective B)
    (hc : B.comp A=A.comp B) (f : E) : B f ∈ (operator A B hi).domain :=
  LinearPMap.mem_domain_of_mem_graph (graph_on_B A B hi hc f)

theorem on_B (A B : E →L[ℂ] E) (hi : Function.Injective B)
    (hc : B.comp A=A.comp B) (f : E) :
    operator A B hi ⟨B f,B_mem_domain A B hi hc f⟩=A f :=
  LinearPMap.mem_graph_snd_inj _ ((operator A B hi).mem_graph ⟨_,B_mem_domain A B hi hc f⟩)
    (graph_on_B A B hi hc f) rfl

theorem operator_dense (A B : E →L[ℂ] E) (hi : Function.Injective B)
    (hc : B.comp A=A.comp B) (hs : ∀ f g,inner ℂ (B f) g=inner ℂ f (B g)) :
    Dense ((operator A B hi).domain : Set E) := by
  apply (symmetric_injective_dense B hs hi).mono
  rintro f ⟨g,rfl⟩
  exact B_mem_domain A B hi hc g

theorem parameterize (A B : E →L[ℂ] E)
    (hc : B.comp A=A.comp B) (hn : A.comp A+B.comp B=ContinuousLinearMap.id ℂ E)
    (f g : E) (h : B g=A f) : B (B f+A g)=f ∧ A (B f+A g)=g := by
  have hcf : B (A f)=A (B f) := congrArg (fun C : E →L[ℂ] E => C f) hc
  have hcg : B (A g)=A (B g) := congrArg (fun C : E →L[ℂ] E => C g) hc
  have hnf : A (A f)+B (B f)=f := congrArg (fun C : E →L[ℂ] E => C f) hn
  have hng : A (A g)+B (B g)=g := congrArg (fun C : E →L[ℂ] E => C g) hn
  constructor
  · rw [map_add,hcg,h,add_comm]
    exact hnf
  · rw [map_add,← hcf,← h,add_comm]
    exact hng

theorem operator_selfAdjoint (A B : E →L[ℂ] E) (hi : Function.Injective B)
    (hc : B.comp A=A.comp B)
    (hn : A.comp A+B.comp B=ContinuousLinearMap.id ℂ E)
    (hsB : ∀ f g,inner ℂ (B f) g=inner ℂ f (B g))
    (hsA : ∀ f g,inner ℂ (A f) g=inner ℂ f (A g)) :
    IsSelfAdjoint (operator A B hi) := by
  let T := operator A B hi
  have hd := operator_dense A B hi hc hsB
  have upper : T.adjoint ≤ T := by
    apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨y,rfl⟩ := (LinearPMap.mem_graph_iff' _).mp hz
    rw [operator_graph,mem_relation]
    apply ext_inner_right ℂ
    intro h
    calc
      inner ℂ (B (T.adjoint y)) h=inner ℂ (T.adjoint y) (B h) := hsB _ _
      _ = inner ℂ y.val (T ⟨B h,B_mem_domain A B hi hc h⟩) :=
        LinearPMap.adjoint_isFormalAdjoint hd y ⟨_,B_mem_domain A B hi hc h⟩
      _ = inner ℂ y.val (A h) := by rw [on_B A B hi hc h]
      _ = inner ℂ (A y.val) h := (hsA _ _).symm
  have lower : T ≤ T.adjoint := by
    have hfml : T.IsFormalAdjoint T := by
      intro f g
      have hf := (mem_relation A B f.val (T f)).1 (by
        rw [← operator_graph A B hi]
        exact T.mem_graph f)
      have hg := (mem_relation A B g.val (T g)).1 (by
        rw [← operator_graph A B hi]
        exact T.mem_graph g)
      obtain ⟨hf₁,hf₂⟩ := parameterize A B hc hn f.val (T f) hf
      obtain ⟨hg₁,hg₂⟩ := parameterize A B hc hn g.val (T g) hg
      let u := B f.val+A (T f)
      let v := B g.val+A (T g)
      change B u=f.val at hf₁
      change A u=T f at hf₂
      change B v=g.val at hg₁
      change A v=T g at hg₂
      rw [← hf₁,← hf₂,← hg₁,← hg₂]
      calc
        inner ℂ (A u) (B v)=inner ℂ u (A (B v)) := hsA _ _
        _ = inner ℂ u (B (A v)) := by
          rw [← ContinuousLinearMap.comp_apply,← hc,ContinuousLinearMap.comp_apply]
        _ = inner ℂ (B u) (A v) := (hsB _ _).symm
    exact hfml.le_adjoint hd
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm upper lower)

end AASCKleinGordon.BoundedPair
