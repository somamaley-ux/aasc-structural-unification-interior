import KGWeylCoherentKernel
import InnerProductGramSpan

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

def coherentSpan (a : Parameters) : Submodule ℂ (FockHilbert a) :=
  LinearMap.range (Finsupp.linearCombination ℂ (exponentialVector a))

theorem coherentSpan_eq_span (a : Parameters) :
    coherentSpan a=Submodule.span ℂ (Set.range (exponentialVector a)) :=
  Finsupp.range_linearCombination ℂ

theorem exponentialVector_mem_coherentSpan (a : Parameters) (f : 𝓢(Momentum,ℂ)) :
    exponentialVector a f∈coherentSpan a := by
  rw [coherentSpan_eq_span]
  exact Submodule.subset_span ⟨f,rfl⟩

def coherentSpanGenerator (a : Parameters) (f : 𝓢(Momentum,ℂ)) : coherentSpan a :=
  ⟨exponentialVector a f,exponentialVector_mem_coherentSpan a f⟩

/-- Actual well-defined linear isometry on the span of original exponential
vectors. Full-Fock extension is a subsequent conclusion requiring proved totality. -/
def weylSpanIsometry (a : Parameters) (g : 𝓢(Momentum,ℂ)) : coherentSpan a →ₗᵢ[ℂ] FockHilbert a :=
  gramSpanIsometry (exponentialVector a) (weylCoherentImage a g) (weylCoherentImage_inner a g)

theorem weylSpanIsometry_generator (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    weylSpanIsometry a g (coherentSpanGenerator a f)=weylCoherentImage a g f := by
  classical
  have h:=gramSpanIsometry_apply_combination (exponentialVector a) (weylCoherentImage a g)
    (weylCoherentImage_inner a g) (Finsupp.single f 1) ⟨Finsupp.single f 1,rfl⟩
  simpa only [Finsupp.linearCombination_single,one_smul] using h

theorem weylSpanIsometry_norm (a : Parameters) (g : 𝓢(Momentum,ℂ)) (u : coherentSpan a) :
    ‖weylSpanIsometry a g u‖=‖(u : FockHilbert a)‖ := (weylSpanIsometry a g).norm_map u

theorem weylSpanIsometry_vacuum (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylSpanIsometry a g (coherentSpanGenerator a 0)=normalizedCoherentVector a g := by
  rw [weylSpanIsometry_generator,weylCoherentImage_vacuum]

end AASCKleinGordon
