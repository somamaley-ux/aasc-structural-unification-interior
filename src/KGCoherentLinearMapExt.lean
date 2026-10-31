import KGCoherentTotality

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem coherentSpan_linearMap_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Parameters) (L M : coherentSpan a →ₗ[ℂ] V)
    (h : ∀ f : 𝓢(Momentum,ℂ),L (coherentSpanGenerator a f)=M (coherentSpanGenerator a f)) : L=M := by
  classical
  apply LinearMap.ext
  rintro ⟨v,hv⟩
  obtain ⟨c,rfl⟩:=hv
  have he : (⟨Finsupp.linearCombination ℂ (exponentialVector a) c,⟨c,rfl⟩⟩ : coherentSpan a)=
      ∑ f∈c.support,c f • coherentSpanGenerator a f := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul]
    rfl
  rw [he]
  simp only [map_sum,map_smul,h]

end AASCKleinGordon
