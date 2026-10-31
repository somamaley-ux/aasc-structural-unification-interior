import EHKGCauchyObservationFaithful

/-! A nonzero smooth compact Cauchy preparation, constructed from an actual
bump on the full central leaf. Its resulting field has value one at the origin. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem exists_nonzero_compact_cauchy_position (a : Parameters) :
    ∃ f : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞), f 0 = 1 := by
  have inside : (0 : KGSpatialSpace) ∈ centralLeafDomain (conformalFrequency a) :=
    Metric.mem_ball_self (protected_radius_positive _)
  obtain ⟨F, support, compact, regular, bounds, one⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      ((centralLeafDomain (conformalFrequency a)).isOpen.mem_nhds inside)
  exact ⟨⟨F, regular, compact, support⟩, one⟩

def occupiedCompactCauchyPosition (a : Parameters) :
    TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞) :=
  Classical.choose (exists_nonzero_compact_cauchy_position a)

theorem occupied_compact_cauchy_position_nonzero (a : Parameters) : occupiedCompactCauchyPosition a ≠ 0 := by
  intro zero
  have one := Classical.choose_spec (exists_nonzero_compact_cauchy_position a)
  change occupiedCompactCauchyPosition a 0 = 1 at one
  rw [zero] at one
  exact zero_ne_one one

theorem occupied_curved_cauchy_field_nonzero (a : Parameters) :
    compactCurvedField a (centralLeafDomain (conformalFrequency a)) (occupiedCompactCauchyPosition a) 0 0 = 1 := by
  rw [compact_curved_initial_position a _ _ _ 0 (by simp)]
  have spaceZero : (coordinateSpatialSplit (0 : CoordinatePoint)).2 = 0 := by simp
  rw [spaceZero]
  exact Classical.choose_spec (exists_nonzero_compact_cauchy_position a)

end AASCKleinGordon.CurvedKG
