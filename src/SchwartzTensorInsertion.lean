import SchwartzProductEstimates

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon.SchwartzOperations
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def tensorLeftCLM (f : 𝓢(E,ℂ)) : 𝓢(F,ℂ) →L[ℂ] 𝓢(E × F,ℂ) := by
  refine SchwartzMap.mkCLM (fun g z => f z.1*g z.2)
    (fun g h z => by simp [mul_add])
    (fun c g z => by simp only [SchwartzMap.smul_apply,smul_eq_mul,RingHom.id_apply]; ring)
    (fun g => ((f.smooth ⊤).comp (ContinuousLinearMap.fst ℝ E F).contDiff).mul
      ((g.smooth ⊤).comp (ContinuousLinearMap.snd ℝ E F).contDiff)) ?_
  rintro ⟨k,n⟩
  let C := ‖realComplexMultiplication‖*(∑ i ∈ Finset.range (n+1),(n.choose i : ℝ))*
    schwartzBound k n f*2^k
  refine ⟨Finset.Iic (k,n),C,?_,?_⟩
  · have := schwartzBound_nonneg k n f
    dsimp [C]
    positivity
  · intro g z
    calc
      _ ≤ ‖realComplexMultiplication‖*(∑ i ∈ Finset.range (n+1),(n.choose i : ℝ))*
          schwartzBound k n f*schwartzBound k n g := tensor_iteratedFDeriv_bound f g k n z
      _ = C*(Finset.Iic (k,n)).sup (schwartzSeminormFamily ℂ F ℂ) g := by
        dsimp [C,schwartzBound]
        ring

@[simp] theorem tensorLeftCLM_apply (f : 𝓢(E,ℂ)) (g : 𝓢(F,ℂ)) (x : E) (y : F) :
    tensorLeftCLM f g (x,y)=f x*g y := rfl

theorem tensor_seminorm_bound (f : 𝓢(E,ℂ)) (g : 𝓢(F,ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (tensorLeftCLM f g)≤
      ‖realComplexMultiplication‖*(∑ i ∈ Finset.range (n+1),(n.choose i : ℝ))*
        schwartzBound k n f*schwartzBound k n g := by
  apply SchwartzMap.seminorm_le_bound ℂ k n (tensorLeftCLM f g)
  · have := schwartzBound_nonneg k n f
    have := schwartzBound_nonneg k n g
    positivity
  · exact tensor_iteratedFDeriv_bound f g k n

theorem tensorLeft_add (f h : 𝓢(E,ℂ)) (g : 𝓢(F,ℂ)) :
    tensorLeftCLM (f+h) g=tensorLeftCLM f g+tensorLeftCLM h g := by
  ext z
  change (f z.1+h z.1)*g z.2=f z.1*g z.2+h z.1*g z.2
  ring

theorem tensorLeft_smul (c : ℂ) (f : 𝓢(E,ℂ)) (g : 𝓢(F,ℂ)) :
    tensorLeftCLM (c • f) g=c • tensorLeftCLM f g := by
  ext z
  change (c*f z.1)*g z.2=c*(f z.1*g z.2)
  ring

end AASCKleinGordon.SchwartzOperations
