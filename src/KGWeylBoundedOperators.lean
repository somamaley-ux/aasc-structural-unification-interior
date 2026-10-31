import KGCoherentTotality
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- The actual bounded displacement on the same original Fock completion.
Both prerequisites for the extension are proved, rather than bridge fields. -/
def weylOperator (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FockHilbert a →L[ℂ] FockHilbert a :=
  (weylSpanIsometry a g).toContinuousLinearMap.extend (coherentSpan a).subtypeL

theorem weylOperator_on_span (a : Parameters) (g : 𝓢(Momentum,ℂ)) (u : coherentSpan a) :
    weylOperator a g u=weylSpanIsometry a g u := by
  exact ContinuousLinearMap.extend_eq _ (coherentSpan_subtype_dense a)
    isUniformEmbedding_subtype_val.isUniformInducing u

theorem weylOperator_exponentialVector (a : Parameters) (g f : 𝓢(Momentum,ℂ)) :
    weylOperator a g (exponentialVector a f)=weylCoherentImage a g f := by
  exact (weylOperator_on_span a g (coherentSpanGenerator a f)).trans
    (weylSpanIsometry_generator a g f)

theorem weylOperator_norm (a : Parameters) (g : 𝓢(Momentum,ℂ)) (u : FockHilbert a) :
    ‖weylOperator a g u‖=‖u‖ := by
  have h : (fun v : FockHilbert a => ‖weylOperator a g v‖)=(fun v => ‖v‖) := by
    apply ((weylOperator a g).continuous.norm).ext_on (coherentSpan_dense a) continuous_norm
    intro v hv
    change ‖weylOperator a g ((⟨v,hv⟩ : coherentSpan a) : FockHilbert a)‖=‖v‖
    rw [weylOperator_on_span]
    exact weylSpanIsometry_norm a g ⟨v,hv⟩
  exact congrFun h u

def weylIsometry (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    FockHilbert a →ₗᵢ[ℂ] FockHilbert a :=
  { (weylOperator a g).toLinearMap with norm_map' := weylOperator_norm a g }

theorem weylOperator_zero (a : Parameters) :
    weylOperator a 0=ContinuousLinearMap.id ℂ (FockHilbert a) := by
  apply continuousLinearMap_eq_on_exponentialVectors a
  intro f
  rw [weylOperator_exponentialVector,weylCoherentImage_zero_displacement]
  rfl

theorem weylOperator_vacuum (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylOperator a g (fockVacuum a)=normalizedCoherentVector a g := by
  rw [← exponentialVector_zero,weylOperator_exponentialVector,weylCoherentImage_vacuum]

end AASCKleinGordon
