import SchwartzPostcomposition

noncomputable section
open scoped SchwartzMap
namespace AASCKleinGordon.SchwartzOperations
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def conjugateSchwartzCLM : 𝓢(E,ℂ) →L[ℝ] 𝓢(E,ℂ) :=
  postcomposeCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp] theorem conjugateSchwartzCLM_apply (h : 𝓢(E,ℂ)) (x : E) :
    conjugateSchwartzCLM h x = star (h x) := rfl

theorem conjugateSchwartz_add (f g : 𝓢(E,ℂ)) :
    conjugateSchwartzCLM (f+g) = conjugateSchwartzCLM f + conjugateSchwartzCLM g :=
  map_add _ _ _

theorem conjugateSchwartz_smul (c : ℂ) (f : 𝓢(E,ℂ)) :
    conjugateSchwartzCLM (c • f) = star c • conjugateSchwartzCLM f := by
  ext x
  change star (c * f x) = star c * star (f x)
  simp [star_mul, mul_comm]

@[simp] theorem conjugateSchwartz_involutive (h : 𝓢(E,ℂ)) :
    conjugateSchwartzCLM (conjugateSchwartzCLM h) = h := by
  ext x
  simp

end AASCKleinGordon.SchwartzOperations
