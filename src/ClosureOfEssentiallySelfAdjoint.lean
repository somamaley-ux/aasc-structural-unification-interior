import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.UnitaryCore
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem closure_eq_adjoint_of_selfAdjoint_adjoint
    (T : H →ₗ.[ℂ] H) (hd : Dense (T.domain : Set H))
    (hsym : T.IsFormalAdjoint T) (hsa : IsSelfAdjoint T.adjoint) : T.closure=T.adjoint := by
  have hle : T≤T.adjoint := hsym.le_adjoint hd
  have hcl : T.IsClosable := LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨T.adjoint,LinearPMap.adjoint_isClosed hd,hle⟩
  have hadj : T.adjoint.IsFormalAdjoint T.adjoint := by
    have h := LinearPMap.adjoint_isFormalAdjoint hsa.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hsa] at h
  have upper : T.graph.topologicalClosure≤T.adjoint.graph :=
    T.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hle) (LinearPMap.adjoint_isClosed hd)
  have lower : T.adjoint.graph≤T.graph.topologicalClosure := by
    intro z hz
    obtain ⟨y,rfl⟩ := (LinearPMap.mem_graph_iff' T.adjoint).mp hz
    let Z := WithLp 2 (H × H)
    let e : (H × H) ≃L[ℂ] Z := (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm
    let S : Submodule ℂ Z := T.graph.map e.toLinearMap
    have hez : e (y.val,T.adjoint y)∈S.topologicalClosure := by
      rw [← S.orthogonal_orthogonal_eq_closure]
      apply (S.orthogonal.mem_orthogonal _).mpr
      intro w hw
      let wp := e.symm w
      have hw0 (u : T.domain) : inner ℂ u.val wp.1+inner ℂ (T u) wp.2=0 := by
        have h := (S.mem_orthogonal w).mp hw (e (u.val,T u))
          ⟨(u.val,T u),LinearPMap.mem_graph T u,rfl⟩
        change inner ℂ (WithLp.toLp 2 (u.val,T u)) w=0 at h
        simpa only [WithLp.prod_inner_apply,WithLp.ofLp_toLp] using h
      have hp (u : T.domain) : inner ℂ (T u) wp.2=inner ℂ u.val (-wp.1) := by
        rw [inner_neg_right]
        linear_combination hw0 u
      have hpa (u : T.domain) : inner ℂ (-wp.1) u.val=inner ℂ wp.2 (T u) := by
        simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hp u).symm
      have hm : wp.2∈T.adjoint.domain :=
        LinearPMap.mem_adjoint_domain_of_exists _ ⟨-wp.1,hpa⟩
      have ha : T.adjoint ⟨wp.2,hm⟩ = -wp.1 := LinearPMap.adjoint_apply_eq hd _ hpa
      have hv : inner ℂ wp.1 y.val+inner ℂ wp.2 (T.adjoint y)=0 := by
        rw [← hadj ⟨wp.2,hm⟩ y,ha,inner_neg_left]
        simp only [add_neg_cancel]
      change inner ℂ w (WithLp.toLp 2 (y.val,T.adjoint y))=0
      simpa only [WithLp.prod_inner_apply,WithLp.ofLp_toLp] using hv
    have hclosed : IsClosed {w : Z | e.symm w∈T.graph.topologicalClosure} :=
      T.graph.isClosed_topologicalClosure.preimage e.symm.continuous
    have hs : (S : Set Z) ⊆ {w : Z | e.symm w∈T.graph.topologicalClosure} := by
      rintro w ⟨v,hv,rfl⟩
      change e.symm (e v)∈T.graph.topologicalClosure
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact T.graph.le_topologicalClosure hv
    have h := closure_minimal hs hclosed hez
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  apply LinearPMap.eq_of_eq_graph
  rw [← hcl.graph_closure_eq_closure_graph]
  exact le_antisymm upper lower

end AASCKleinGordon.UnitaryCore
