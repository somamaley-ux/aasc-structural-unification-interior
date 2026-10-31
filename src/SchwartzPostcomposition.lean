import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon.SchwartzOperations
variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def postcomposeCLM (L : V →L[ℝ] W) : 𝓢(E,V) →L[ℝ] 𝓢(E,W) := by
  refine SchwartzMap.mkCLM (fun f x => L (f x))
    (fun _ _ _ => L.map_add _ _) (fun c f x => L.map_smul c (f x))
    (fun f => L.contDiff.comp (f.smooth ⊤)) ?_
  rintro ⟨k,n⟩
  refine ⟨{(k,n)},‖L‖,norm_nonneg _,?_⟩
  intro f x
  simp only [Finset.sup_singleton]
  change _ ≤ ‖L‖ * SchwartzMap.seminorm ℝ k n f
  have h := L.norm_iteratedFDeriv_comp_left (f.contDiffAt ⊤ (x:=x)) (n:=n) (by exact_mod_cast le_top)
  calc
    _ ≤ ‖x‖^k*(‖L‖*‖iteratedFDeriv ℝ n f x‖) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = ‖L‖*(‖x‖^k*‖iteratedFDeriv ℝ n f x‖) := by ring
    _ ≤ ‖L‖*SchwartzMap.seminorm ℝ k n f :=
      mul_le_mul_of_nonneg_left (f.le_seminorm ℝ k n x) (norm_nonneg _)

@[simp] theorem postcomposeCLM_apply (L : V →L[ℝ] W) (f : 𝓢(E,V)) (x : E) :
    postcomposeCLM L f x=L (f x) := rfl

end AASCKleinGordon.SchwartzOperations
