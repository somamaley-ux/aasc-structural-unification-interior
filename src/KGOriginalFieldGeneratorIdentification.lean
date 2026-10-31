import KGOriginalFieldClosure
import KGWeylMaximalGenerator

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Equality of partial operators includes equality of their actual domains. -/
theorem originalWeylField_closure_eq_maximalGenerator (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (originalWeylField a g).closure=weylOrbitGenerator a g := by
  rw [originalWeylField_closure_eq_coherentAdjoint,weylOrbitGenerator_eq_coherentAdjoint]

/-- The original real field, with its explicit amplitude and original signs. -/
theorem original_real_field_closure_eq_maximalGenerator (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) :
    (fockSpacetimeField a s h.val).closure=
      weylOrbitGenerator a (realFieldWeylLabelCLM a s h) := by
  rw [← originalWeylField_real_label a s h]
  exact originalWeylField_closure_eq_maximalGenerator a (realFieldWeylLabelCLM a s h)

/-- The closure domain is exactly the genuine norm-differentiability domain,
not an assumed generator certificate or the finite-particle core. -/
theorem original_real_field_closure_domain (a : Parameters) (s : ℝ)
    (h : realSpacetimeTestSpace) (v : FockHilbert a) :
    v∈(fockSpacetimeField a s h.val).closure.domain ↔
      DifferentiableAt ℝ (fun t : ℝ => realFieldWeylGroup a s h t v) 0 := by
  rw [original_real_field_closure_eq_maximalGenerator]
  rfl

end AASCKleinGordon
