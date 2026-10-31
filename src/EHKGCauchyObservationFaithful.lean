import EHKGScalarUseState

/-! Actual position and normal observations separate all compact Cauchy
pairs on the entire declared leaf. No data information is discarded in the
constructed field/use map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem compact_test_zero_outside (U : Opens KGSpatialSpace) (f : TestFunction U ℝ (⊤ : ℕ∞))
    (x : KGSpatialSpace) (outside : x ∉ U) : f x = 0 := by
  by_contra nonzero
  exact outside (f.tsupport_subset (subset_closure nonzero))

theorem compact_cauchy_observations_faithful (a : Parameters)
    (f h g k : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (answers : ∀ q, scalarQuestionAnswer a (initialCurvedScalarUseState a f h) q =
      scalarQuestionAnswer a (initialCurvedScalarUseState a g k) q) : f = g ∧ h = k := by
  constructor
  · ext x
    by_cases inside : x ∈ centralLeafDomain (conformalFrequency a)
    · have equal := answers (.value (centralLeafPoint x))
      rw [initial_scalar_position_answer a f h x inside, initial_scalar_position_answer a g k x inside] at equal
      exact Option.some.inj equal
    · rw [compact_test_zero_outside _ f x inside, compact_test_zero_outside _ g x inside]
  · ext x
    by_cases inside : x ∈ centralLeafDomain (conformalFrequency a)
    · have equal := answers (.normal (centralLeafPoint x))
      rw [initial_scalar_normal_answer a f h x inside, initial_scalar_normal_answer a g k x inside] at equal
      exact Option.some.inj equal
    · rw [compact_test_zero_outside _ h x inside, compact_test_zero_outside _ k x inside]

end AASCKleinGordon.CurvedKG
