import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
set_option maxHeartbeats 1600000
namespace AASCKleinGordon

section
variable {I H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (v : I → H) (w : I → K) (gram : ∀ i j,inner ℂ (w i) (w j)=inner ℂ (v i) (v j))
include gram

theorem linearCombination_inner_of_gram (c d : I →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ w c) (Finsupp.linearCombination ℂ w d)=
      inner ℂ (Finsupp.linearCombination ℂ v c) (Finsupp.linearCombination ℂ v d) := by
  classical
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,gram]

theorem linearCombination_kernel_of_gram :
    LinearMap.ker (Finsupp.linearCombination ℂ v)≤LinearMap.ker (Finsupp.linearCombination ℂ w) := by
  intro c hc
  change Finsupp.linearCombination ℂ w c=0
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [linearCombination_inner_of_gram v w gram]
  change Finsupp.linearCombination ℂ v c=0 at hc
  rw [hc,inner_zero_left]

/-- Gram preservation proves well-defined linear descent from actual finite
linear combinations. No linear independence or density is assumed. -/
def gramSpanLinearMap : LinearMap.range (Finsupp.linearCombination ℂ v) →ₗ[ℂ] K :=
  ((LinearMap.ker (Finsupp.linearCombination ℂ v)).liftQ
    (Finsupp.linearCombination ℂ w) (linearCombination_kernel_of_gram v w gram)).comp
      (Finsupp.linearCombination ℂ v).quotKerEquivRange.symm.toLinearMap

theorem gramSpanLinearMap_apply_combination (c : I →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ v c∈LinearMap.range (Finsupp.linearCombination ℂ v)) :
    gramSpanLinearMap v w gram ⟨Finsupp.linearCombination ℂ v c,hc⟩=
      Finsupp.linearCombination ℂ w c := by
  simp only [gramSpanLinearMap,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearMap.quotKerEquivRange_symm_apply_image,Submodule.liftQ_apply]
  rfl

theorem gramSpanLinearMap_inner (x y : LinearMap.range (Finsupp.linearCombination ℂ v)) :
    inner ℂ (gramSpanLinearMap v w gram x) (gramSpanLinearMap v w gram y)=inner ℂ x y := by
  obtain ⟨c,hc⟩:=x.property
  obtain ⟨d,hd⟩:=y.property
  have hx : x=⟨Finsupp.linearCombination ℂ v c,⟨c,rfl⟩⟩:=Subtype.ext hc.symm
  have hy : y=⟨Finsupp.linearCombination ℂ v d,⟨d,rfl⟩⟩:=Subtype.ext hd.symm
  rw [hx,hy,gramSpanLinearMap_apply_combination,gramSpanLinearMap_apply_combination]
  exact linearCombination_inner_of_gram v w gram c d

def gramSpanIsometry : LinearMap.range (Finsupp.linearCombination ℂ v) →ₗᵢ[ℂ] K :=
  (gramSpanLinearMap v w gram).isometryOfInner (gramSpanLinearMap_inner v w gram)

theorem gramSpanIsometry_apply_combination (c : I →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ v c∈LinearMap.range (Finsupp.linearCombination ℂ v)) :
    gramSpanIsometry v w gram ⟨Finsupp.linearCombination ℂ v c,hc⟩=
      Finsupp.linearCombination ℂ w c := gramSpanLinearMap_apply_combination v w gram c hc

end
end AASCKleinGordon
