import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin

namespace AASCSemanticExhaustion
open scoped BigOperators

theorem sum_fin_twenty (f : Fin 20 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 +
      (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 +
      (f 12 + (f 13 + (f 14 + (f 15 + (f 16 + (f 17 +
      (f 18 + (f 19 + 0))))))))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

#print axioms sum_fin_twenty
end AASCSemanticExhaustion
