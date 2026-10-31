import KGCoherentGraphCore

noncomputable section
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem partial_closure_le_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T S : H →ₗ.[ℂ] H) (hc : T.IsClosable) (hs : S.IsClosed) (hle : T≤S) : T.closure≤S := by
  apply LinearPMap.le_of_le_graph
  rw [← hc.graph_closure_eq_closure_graph]
  exact T.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hle) hs

theorem originalWeylField_le_coherentAdjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    originalWeylField a g≤(weylCoherentCoreGenerator a g).adjoint := by
  have hp : (originalWeylField a g).closure≤(originalWeylField a g).adjoint :=
    partial_closure_le_closed _ _ (originalWeylField_closable a g)
      (LinearPMap.adjoint_isClosed (finiteParticleCoreToFock_dense a))
      ((originalWeylField_symmetric a g).le_adjoint (finiteParticleCoreToFock_dense a))
  have hs:weylCoherentCoreGenerator a g≤(originalWeylField a g).adjoint :=
    le_trans (weylCoherentCoreGenerator_le_original_closure a g) hp
  have hf : (weylCoherentCoreGenerator a g).IsFormalAdjoint (originalWeylField a g) := by
    intro x y
    have hh:=(originalWeylField a g).adjoint_isFormalAdjoint (finiteParticleCoreToFock_dense a)
      ⟨x.val,hs.1 x.property⟩ y
    have he:=hs.2 (x:=x) (y:=⟨x.val,hs.1 x.property⟩) rfl
    simpa only [← he] using hh
  exact hf.le_adjoint (coherentSpan_dense a)

theorem originalWeylField_closure_eq_coherentAdjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (originalWeylField a g).closure=(weylCoherentCoreGenerator a g).adjoint := by
  have upper := partial_closure_le_closed _ _ (originalWeylField_closable a g)
    (LinearPMap.adjoint_isClosed (coherentSpan_dense a))
    (originalWeylField_le_coherentAdjoint a g)
  have hsc : (weylCoherentCoreGenerator a g).IsClosable :=
    LinearPMap.isClosable_iff_exists_closed_extension.mpr
      ⟨(weylCoherentCoreGenerator a g).adjoint,LinearPMap.adjoint_isClosed (coherentSpan_dense a),
        (weylCoherentCoreGenerator_symmetric a g).le_adjoint (coherentSpan_dense a)⟩
  have lower:=partial_closure_le_closed _ _ hsc
    (originalWeylField_closable a g).closure_isClosed
    (weylCoherentCoreGenerator_le_original_closure a g)
  rw [weylCoherentCoreGenerator_closure_eq_adjoint] at lower
  exact le_antisymm upper lower

theorem originalWeylField_closure_selfAdjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    IsSelfAdjoint (originalWeylField a g).closure := by
  rw [originalWeylField_closure_eq_coherentAdjoint]
  exact weylCoherentCoreGenerator_adjoint_selfAdjoint a g

/-- Every original core vector is covered, without a factorization assumption. -/
theorem originalWeylField_original_core_hasDerivAt (a : Parameters) (g : 𝓢(Momentum,ℂ))
    (u : FiniteParticleCore) (r : ℝ) :
    HasDerivAt (fun t : ℝ => weylRealLine a g t (finiteParticleCoreToFock a u))
      (Complex.I • weylRealLine a g r (finiteParticleCoreToFock a (originalWeylCoreGenerator a g u))) r := by
  have hle:=originalWeylField_le_coherentAdjoint a g
  let x:=includedFockCore a u
  have hh:=weylCoherentCoreGenerator_adjoint_hasDerivAt a g ⟨x.val,hle.1 x.property⟩ r
  have he:=hle.2 (x:=x) (y:=⟨x.val,hle.1 x.property⟩) rfl
  rw [← he] at hh
  simpa only [x,includedFockCore_val,originalWeylField_on_original_core] using hh

/-- The requested exact full original-core derivative with the fixed original
field signs and its explicit amplitude s. It also holds at s=0; no calibration
value or nonzero-amplitude conclusion is inferred here. -/
theorem original_real_field_full_core_weyl_derivative (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) (u : FiniteParticleCore) (r : ℝ) :
    HasDerivAt (fun t : ℝ => realFieldWeylGroup a s h t (finiteParticleCoreToFock a u))
      (Complex.I • realFieldWeylGroup a s h r
        (finiteParticleCoreToFock a (spacetimeFieldCore a s h.val u))) r := by
  simpa only [originalWeylCoreGenerator_real_label] using
    originalWeylField_original_core_hasDerivAt a (realFieldWeylLabelCLM a s h) u r

theorem original_real_field_closure_selfAdjoint (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) : IsSelfAdjoint (fockSpacetimeField a s h.val).closure := by
  rw [← originalWeylField_real_label a s h]
  exact originalWeylField_closure_selfAdjoint a (realFieldWeylLabelCLM a s h)

end AASCKleinGordon
