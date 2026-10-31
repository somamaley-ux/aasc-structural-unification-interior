import KGWeylCoherentCoreGenerator

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem weylCoherentAdjoint_le_maximalGenerator (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    (weylCoherentCoreGenerator a g).adjoint≤weylOrbitGenerator a g := by
  refine ⟨?_,?_⟩
  · intro v hv
    change DifferentiableAt ℝ (fun t : ℝ => weylRealLine a g t v) 0
    exact (weylCoherentCoreGenerator_adjoint_hasDerivAt a g ⟨v,hv⟩ 0).differentiableAt
  · intro x y hxy
    have hx:=weylCoherentCoreGenerator_adjoint_hasDerivAt a g x 0
    simp only [weylRealLine_zero] at hx
    have he:=hx.deriv
    rw [weylOrbitGenerator_apply,← hxy,he,smul_smul]
    simp only [neg_mul,Complex.I_mul_I,neg_neg,one_smul]

theorem weylOrbitGenerator_eq_coherentAdjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    weylOrbitGenerator a g=(weylCoherentCoreGenerator a g).adjoint := by
  have hsa:=weylCoherentCoreGenerator_adjoint_selfAdjoint a g
  have hle:=weylCoherentAdjoint_le_maximalGenerator a g
  have hanti:=UnitaryCore.adjoint_antitone_of_dense
    (weylCoherentCoreGenerator a g).adjoint (weylOrbitGenerator a g) hsa.dense_domain hle
  rw [LinearPMap.isSelfAdjoint_def.mp hsa] at hanti
  have hsym:=(weylOrbitGenerator_symmetric a g).le_adjoint (weylOrbitGenerator_domain_dense a g)
  exact le_antisymm (le_trans hsym hanti) hle

theorem weylOrbitGenerator_selfAdjoint (a : Parameters) (g : 𝓢(Momentum,ℂ)) :
    IsSelfAdjoint (weylOrbitGenerator a g) := by
  rw [weylOrbitGenerator_eq_coherentAdjoint]
  exact weylCoherentCoreGenerator_adjoint_selfAdjoint a g

end AASCKleinGordon
