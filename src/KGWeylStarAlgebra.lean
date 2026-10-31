import KGWeylObservableAlgebra
import KGWeylContinuity
import StarStableAdjoin

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

theorem globalWeylAlgebra_star_mem (a : Parameters)
    {T : FockHilbert a →L[ℂ] FockHilbert a} (hT : T∈globalWeylAlgebra a) :
    star T∈globalWeylAlgebra a := by
  apply algebra_adjoin_star_mem (Set.range (weylOperator a)) _ hT
  rintro S ⟨g,rfl⟩
  rw [ContinuousLinearMap.star_eq_adjoint,weylOperator_adjoint]
  exact weylOperator_mem_globalWeylAlgebra a (-g)

/-- The concrete bounded observable algebra carries its actual Hilbert adjoint. -/
def globalWeylStarAlgebra (a : Parameters) :
    StarSubalgebra ℂ (FockHilbert a →L[ℂ] FockHilbert a) :=
  { globalWeylAlgebra a with star_mem' := fun h => globalWeylAlgebra_star_mem a h }

theorem globalWeylStarAlgebra_toSubalgebra (a : Parameters) :
    (globalWeylStarAlgebra a).toSubalgebra=globalWeylAlgebra a := rfl

end AASCKleinGordon
