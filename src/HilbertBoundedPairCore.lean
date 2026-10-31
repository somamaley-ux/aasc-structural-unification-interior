import HilbertBoundedPair

noncomputable section
namespace AASCKleinGordon.BoundedPair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem closure_eq_of_dense_invariant_core (A B : E →L[ℂ] E) (hi : Function.Injective B)
    (hc : B.comp A=A.comp B) (hn : A.comp A+B.comp B=ContinuousLinearMap.id ℂ E)
    (C : E →ₗ.[ℂ] E) (hd : Dense (C.domain : Set E))
    (hle : C ≤ operator A B hi) (hB : ∀ f : C.domain,B f.val ∈ C.domain) :
    C.closure=operator A B hi := by
  let T := operator A B hi
  have hclosed : T.IsClosed := operator_closed A B hi
  have hclosable : C.IsClosable := LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨T,hclosed,hle⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hclosable.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle) hclosed
  · intro z hz
    have hz' := (mem_relation A B z.1 z.2).1 (by rwa [← operator_graph A B hi])
    obtain ⟨h1,h2⟩ := parameterize A B hc hn z.1 z.2 hz'
    let w := B z.1+A z.2
    let G : E →L[ℂ] E × E := B.prod A
    have hG : G w=z := Prod.ext h1 h2
    have hw : w ∈ closure (C.domain : Set E) := hd w
    have hgc : G w ∈ closure (G '' (C.domain : Set E)) :=
      image_closure_subset_closure_image G.continuous ⟨w,hw,rfl⟩
    change z ∈ closure (C.graph : Set (E × E))
    rw [← hG]
    apply closure_mono ?_ hgc
    rintro q ⟨f,hf,rfl⟩
    let bf : C.domain := ⟨B f,hB ⟨f,hf⟩⟩
    have hcg := LinearPMap.le_graph_of_le hle (C.mem_graph bf)
    have heq : C bf=A f := LinearPMap.mem_graph_snd_inj T hcg (graph_on_B A B hi hc f) rfl
    change (B f,A f) ∈ C.graph
    rw [← heq]
    exact C.mem_graph bf

end AASCKleinGordon.BoundedPair
