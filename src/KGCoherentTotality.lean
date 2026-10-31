import KGL2BosonicPolarization
import KGL2ProductTotality
import KGWeylCoherentSpan

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Actual exponential vectors are total on the same original Fock Hilbert
space, by scalar-series uniqueness, bosonic polarization and native L2 products. -/
theorem exponentialVector_total (a : Parameters) (v : FockHilbert a)
    (h : ∀ f : 𝓢(Momentum,ℂ),inner ℂ v (exponentialVector a f)=0) : v=0 := by
  apply lp.ext
  funext n
  apply Subtype.ext
  apply particleL2Product_total a n (v n).val
  intro f
  exact inner_eq_zero_symm.mp
    (exponentialVector_orthogonal_forces_sector_product_orthogonality a v h n f)

theorem coherentSpan_closure_eq_top (a : Parameters) : (coherentSpan a).topologicalClosure=⊤ := by
  apply (coherentSpan a).topologicalClosure_eq_top_iff.mpr
  apply le_antisymm _ bot_le
  intro v hv
  change v=0
  apply exponentialVector_total a v
  intro f
  exact ((coherentSpan a).mem_orthogonal' v).mp hv _ (exponentialVector_mem_coherentSpan a f)

theorem coherentSpan_dense (a : Parameters) : Dense (coherentSpan a : Set (FockHilbert a)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (coherentSpan_closure_eq_top a)

theorem coherentSpan_subtype_dense (a : Parameters) : DenseRange (coherentSpan a).subtypeL := by
  change DenseRange (Subtype.val : coherentSpan a → FockHilbert a)
  simpa only [DenseRange,Subtype.range_coe_subtype,Set.setOf_mem_eq] using coherentSpan_dense a

theorem continuousLinearMap_eq_on_exponentialVectors {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] (a : Parameters)
    (F G : FockHilbert a →L[ℂ] K)
    (h : ∀ f : 𝓢(Momentum,ℂ),F (exponentialVector a f)=G (exponentialVector a f)) : F=G := by
  have he : (F : FockHilbert a → K)=G := by
    apply F.continuous.ext_on (coherentSpan_dense a) G.continuous
    rintro u ⟨c,rfl⟩
    simp only [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,h]
  exact ContinuousLinearMap.coeFn_injective he

end AASCKleinGordon
