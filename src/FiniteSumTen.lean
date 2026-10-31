import FiniteSumTwenty
namespace AASCSemanticExhaustion
open scoped BigOperators
theorem sum_fin_ten (f : Fin 10 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 +
      (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + 0))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl
#print axioms sum_fin_ten
end AASCSemanticExhaustion
