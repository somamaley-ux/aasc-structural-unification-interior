import EHKGCompactFinitePropagation

/-! Exact initial-leaf support system. Noncentral sections need not be
Cauchy for the whole diamond, and their open-ball compactness is not asserted. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

theorem central_cauchy_trace_support_exact (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    tsupport (fun x => compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h (centralLeafPoint x)) = tsupport f ∧
    tsupport (fun x => actualNormalDerivative (conformalFrequency a)
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) (centralLeafPoint x)) = tsupport h := by
  have value : (fun x => compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h (centralLeafPoint x)) = f := by
    funext x
    simpa only [central_leaf_space] using compact_curved_initial_position a _ f h (centralLeafPoint x) (central_leaf_time x)
  have normal : (fun x => actualNormalDerivative (conformalFrequency a)
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) (centralLeafPoint x)) = h :=
    funext (compact_curved_initial_normal a f h)
  rw [value, normal]
  exact ⟨rfl, rfl⟩

theorem retained_compact_cauchy_support_system (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    IsCompact (tsupport f ∪ tsupport h) ∧
    tsupport f ∪ tsupport h ⊆ centralLeafDomain (conformalFrequency a) ∧
    tsupport (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) ∩
      protectedDiamond (conformalFrequency a) ⊆ metricCausalShadow (conformalFrequency a) (tsupport f ∪ tsupport h) :=
  ⟨f.hasCompactSupport.union h.hasCompactSupport, union_subset f.tsupport_subset h.tsupport_subset,
    compact_curved_closed_support_in_metric_causal_shadow a f h⟩

end AASCKleinGordon.CurvedKG
