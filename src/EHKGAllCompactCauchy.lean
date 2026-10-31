import EHKGSameMetricUniqueness

/-! The actual solution and arbitrary-local-smooth uniqueness for every
compact smooth real data pair on the declared central leaf. Uniqueness is
equality on the open domain, not equality of arbitrary outside extensions.
The LF evolution topology, same-action and original-use endpoints are later
proofs; they are not fields silently included in this proposition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG

def SameEHKGHistory (a : Parameters) (u : CoordinatePoint → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) u (protectedDiamond (conformalFrequency a)) ∧
    ∀ p ∈ protectedDiamond (conformalFrequency a),
      scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) u p =
        (massWaveNumber a) ^ 2 * u p

def SameEHCompactCauchyTrace (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (u : CoordinatePoint → ℝ) : Prop :=
  ∀ x ∈ centralLeafDomain (conformalFrequency a),
    u (centralLeafPoint x) = f x ∧ actualNormalDerivative (conformalFrequency a) u (centralLeafPoint x) = h x

theorem all_compact_same_eh_cauchy_exists_unique (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    let u := compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h
    SameEHKGHistory a u ∧ SameEHCompactCauchyTrace a f h u ∧
      ∀ v : CoordinatePoint → ℝ, SameEHKGHistory a v → SameEHCompactCauchyTrace a f h v →
        EqOn v u (protectedDiamond (conformalFrequency a)) := by
  let u := compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h
  have history : SameEHKGHistory a u := ⟨(compact_curved_field_smooth a _ f h).contDiffOn,
    fun p hp => compact_curved_field_equation a _ f h p (protected_diamond_subset_ball _ hp)⟩
  have trace : SameEHCompactCauchyTrace a f h u := by
    intro x hx
    constructor
    · simpa only [central_leaf_space] using (compact_curved_initial_position a _ f h
        (centralLeafPoint x) (central_leaf_time x))
    · exact compact_curved_initial_normal a f h x
  refine ⟨history, trace, ?_⟩
  intro v historyV traceV p hp
  exact same_eh_local_smooth_unique a v u historyV.1 history.1 historyV.2 history.2
    (fun x hx => (traceV x hx).1.trans (trace x hx).1.symm)
    (fun x hx => (traceV x hx).2.trans (trace x hx).2.symm) p hp

theorem admitted_nonflat_branch_all_compact_cauchy (a : Parameters) :
    conformalOperand (conformalFrequency a) ∈ wickOriginalMetricNeighborhood (⊤ : Opens CoordinatePoint) ∧
      (0 : CoordinatePoint) ∈ protectedDiamond (conformalFrequency a) ∧
      EHGloballyHyperbolicOn (conformalFrequency a) (protectedDiamond (conformalFrequency a)) ∧
      loweredConnectionCurvature (originalEHActMetric (conformalOperand (conformalFrequency a)))
        (leviCivitaCoefficients (originalEHActMetric (conformalOperand (conformalFrequency a)))) 0 0 1 0 1 ≠ 0 ∧
      ∀ f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞),
        ∃ u : CoordinatePoint → ℝ, SameEHKGHistory a u ∧ SameEHCompactCauchyTrace a f h u ∧
          ∀ v : CoordinatePoint → ℝ, SameEHKGHistory a v → SameEHCompactCauchyTrace a f h v →
            EqOn v u (protectedDiamond (conformalFrequency a)) := by
  refine ⟨(protected_same_eh_nonflat a).2.1, protected_diamond_zero _,
    protected_diamond_globally_hyperbolic _, (protected_same_eh_nonflat a).2.2, ?_⟩
  intro f h
  exact ⟨compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h,
    all_compact_same_eh_cauchy_exists_unique a f h⟩

end AASCKleinGordon.CurvedKG
