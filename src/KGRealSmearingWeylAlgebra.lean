import KGRealSmearingDensity
import KGWeylNonvacuity

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Constructed bounded displacements indexed by the actual original real
spacetime tests and the declared Segal-field amplitude. Generator attachment is
a separate theorem; it is not a field of this definition. -/
def realSmearingWeylOperator (a : Parameters) (s : ℝ) (h : realSpacetimeTestSpace) :
    FockHilbert a →L[ℂ] FockHilbert a :=
  weylOperator a (realFieldWeylLabelCLM a s h)

def realSmearingWeylAlgebra (a : Parameters) (s : ℝ) :
    Subalgebra ℂ (FockHilbert a →L[ℂ] FockHilbert a) :=
  Algebra.adjoin ℂ (Set.range (realSmearingWeylOperator a s))

theorem realSmearingWeyl_range (a : Parameters) (s : ℝ) (hs : s≠0) :
    Set.range (realSmearingWeylOperator a s)=Set.range (weylOperator a) := by
  ext T
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨realFieldWeylLabelCLM a s h,rfl⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨h,hh⟩:=realFieldWeylLabel_surjective a s hs g
    exact ⟨h,congrArg (weylOperator a) hh⟩

theorem realSmearingWeylAlgebra_eq_global (a : Parameters) (s : ℝ) (hs : s≠0) :
    realSmearingWeylAlgebra a s=globalWeylAlgebra a := by
  unfold realSmearingWeylAlgebra globalWeylAlgebra
  rw [realSmearingWeyl_range a s hs]

theorem realSmearingWeylAlgebra_irreducible (a : Parameters) (s : ℝ) (hs : s≠0) :
    GlobalCharge.ObservableIrreducible (realSmearingWeylAlgebra a s) := by
  rw [realSmearingWeylAlgebra_eq_global a s hs]
  exact globalWeylAlgebra_irreducible a

theorem realSmearingWeylAlgebra_star_mem (a : Parameters) (s : ℝ)
    {T : FockHilbert a →L[ℂ] FockHilbert a} (hT : T∈realSmearingWeylAlgebra a s) :
    star T∈realSmearingWeylAlgebra a s := by
  apply algebra_adjoin_star_mem (Set.range (realSmearingWeylOperator a s)) _ hT
  rintro S ⟨h,rfl⟩
  change star (weylOperator a (realFieldWeylLabelCLM a s h))∈_
  rw [ContinuousLinearMap.star_eq_adjoint,weylOperator_adjoint]
  have hh : weylOperator a (-realFieldWeylLabelCLM a s h)=realSmearingWeylOperator a s (-h) := by
    simp only [realSmearingWeylOperator,map_neg]
  rw [hh]
  exact Algebra.subset_adjoin ⟨-h,rfl⟩

def realSmearingWeylStarAlgebra (a : Parameters) (s : ℝ) :
    StarSubalgebra ℂ (FockHilbert a →L[ℂ] FockHilbert a) :=
  {realSmearingWeylAlgebra a s with star_mem':=fun h => realSmearingWeylAlgebra_star_mem a s h}

theorem realSmearingWeylStarAlgebra_eq_global (a : Parameters) (s : ℝ) (hs : s≠0) :
    realSmearingWeylStarAlgebra a s=globalWeylStarAlgebra a := by
  apply SetLike.ext
  intro T
  change T∈realSmearingWeylAlgebra a s ↔ T∈globalWeylAlgebra a
  rw [realSmearingWeylAlgebra_eq_global a s hs]

def realSmearingWeylClosedAlgebra (a : Parameters) (s : ℝ) :
    StarSubalgebra ℂ (FockHilbert a →L[ℂ] FockHilbert a) :=
  (realSmearingWeylStarAlgebra a s).topologicalClosure

/-- Exact algebraic surjectivity, rather than strong approximation, justifies
this equality of the operator-norm closures. -/
theorem realSmearingWeylClosedAlgebra_eq_global (a : Parameters) (s : ℝ) (hs : s≠0) :
    realSmearingWeylClosedAlgebra a s=globalWeylClosedAlgebra a := by
  unfold realSmearingWeylClosedAlgebra globalWeylClosedAlgebra
  rw [realSmearingWeylStarAlgebra_eq_global a s hs]

theorem realSmearingWeylClosedAlgebra_irreducible (a : Parameters) (s : ℝ) (hs : s≠0) :
    GlobalCharge.ObservableIrreducible (realSmearingWeylClosedAlgebra a s).toSubalgebra := by
  rw [realSmearingWeylClosedAlgebra_eq_global a s hs]
  exact globalWeylClosedAlgebra_irreducible a

theorem realSmearingWeyl_moves_vacuum (a : Parameters) (s : ℝ) (hs : s≠0) :
    ∃ h : realSpacetimeTestSpace,realSmearingWeylOperator a s h (fockVacuum a)≠fockVacuum a := by
  obtain ⟨g,hg⟩:=exists_weyl_displacement_moving_vacuum a
  obtain ⟨h,hh⟩:=realFieldWeylLabel_surjective a s hs g
  refine ⟨h,?_⟩
  simpa only [realSmearingWeylOperator,hh] using hg

end AASCKleinGordon
