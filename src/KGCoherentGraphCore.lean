import KGCoherentCoreTruncations
import KGCoherentLinearMapExt

noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
open Filter
open scoped SchwartzMap Topology
namespace AASCKleinGordon

theorem coherentCreationTangent_generator (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    (-Complex.I) • (coherentCreationTangent a g f-
      inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) • exponentialVector a f)=
        weylCoherentCoreGenerator a g (coherentSpanGenerator a f) := by
  have hs:=weylCoherentCoreGenerator_hasDerivAt a g (coherentSpanGenerator a f) 0
  simp only [weylRealLine_zero] at hs
  have hw:=weylRealLine_exponentialVector_hasDerivAt_zero a g f
  have hv : Complex.I • weylCoherentCoreGenerator a g (coherentSpanGenerator a f)=
      coherentWeylVelocity a g f := hs.unique hw
  change (-Complex.I) • (coherentWeylVelocity a g f+
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) • exponentialVector a f-
    inner ℂ (oneParticleSchwartzToHilbert a g) (oneParticleSchwartzToHilbert a f) • exponentialVector a f)=_
  rw [add_sub_cancel_right,← hv,smul_smul]
  simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]

theorem coherentTruncationCore_graph_tendsto (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    Tendsto (fun N : ℕ =>
      (finiteParticleCoreToFock a (coherentTruncationCore f (N+1)),
       originalWeylField a g (includedFockCore a (coherentTruncationCore f (N+1))))) atTop
      (𝓝 (exponentialVector a f,weylCoherentCoreGenerator a g (coherentSpanGenerator a f))) := by
  have hx:=(coherentTruncationCore_tendsto a f).comp (tendsto_add_atTop_nat 1)
  have hc:=(coherentTruncationCore_creation_tendsto a g f).comp (tendsto_add_atTop_nat 1)
  have ha:=coherentTruncationCore_annihilation_tendsto a g f
  have hy:= (hc.sub ha).const_smul (-Complex.I)
  have he : (fun N : ℕ => originalWeylField a g (includedFockCore a (coherentTruncationCore f (N+1))))=
      (fun N : ℕ => (-Complex.I) •
        (finiteParticleCoreToFock a (creationCore g (coherentTruncationCore f (N+1)))-
         finiteParticleCoreToFock a (annihilationCore a g (coherentTruncationCore f (N+1))))) := by
    funext N
    rw [originalWeylField_on_original_core]
    simp only [originalWeylCoreGenerator,LinearMap.smul_apply,LinearMap.sub_apply,map_smul,map_sub]
  rw [coherentCreationTangent_generator] at hy
  have hy' : Tendsto (fun N : ℕ => originalWeylField a g
      (includedFockCore a (coherentTruncationCore f (N+1)))) atTop
      (𝓝 (weylCoherentCoreGenerator a g (coherentSpanGenerator a f))) := by
    rw [he]
    exact hy
  exact hx.prodMk_nhds hy' 

theorem coherent_generator_mem_original_closure_graph (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    (exponentialVector a f,weylCoherentCoreGenerator a g (coherentSpanGenerator a f))∈
      (originalWeylField a g).closure.graph := by
  rw [← (originalWeylField_closable a g).graph_closure_eq_closure_graph]
  apply (originalWeylField a g).graph.isClosed_topologicalClosure.mem_of_tendsto
    (coherentTruncationCore_graph_tendsto a g f)
  exact Eventually.of_forall (fun N => (originalWeylField a g).graph.le_topologicalClosure
    (LinearPMap.mem_graph (originalWeylField a g)
      (includedFockCore a (coherentTruncationCore f (N+1)))))

theorem weylCoherentCoreGenerator_le_original_closure (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylCoherentCoreGenerator a g≤(originalWeylField a g).closure := by
  have hd : coherentSpan a≤(originalWeylField a g).closure.domain := by
    rw [coherentSpan_eq_span]
    apply Submodule.span_le.mpr
    rintro v ⟨f,rfl⟩
    obtain ⟨y,hy,_⟩:= (LinearPMap.mem_graph_iff _).mp
      (coherent_generator_mem_original_closure_graph a g f)
    change y.val=exponentialVector a f at hy
    rw [← hy]
    exact y.property
  let L : coherentSpan a →ₗ[ℂ] FockHilbert a :=
    (originalWeylField a g).closure.toFun.comp (Submodule.inclusion hd)
  have he : (weylCoherentCoreGenerator a g).toFun=L := by
    apply coherentSpan_linearMap_ext a
    intro f
    exact LinearPMap.mem_graph_snd_inj _
      (coherent_generator_mem_original_closure_graph a g f)
      (LinearPMap.mem_graph _ ⟨exponentialVector a f,hd (exponentialVector_mem_coherentSpan a f)⟩) rfl
  refine ⟨hd,?_⟩
  intro x y hxy
  have hx:=congrArg (fun K : coherentSpan a →ₗ[ℂ] FockHilbert a => K x) he
  change weylCoherentCoreGenerator a g x=(originalWeylField a g).closure
    ⟨x.val,hd x.property⟩ at hx
  exact hx.trans (congrArg (originalWeylField a g).closure (Subtype.ext hxy))

end AASCKleinGordon
