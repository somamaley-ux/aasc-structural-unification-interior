import EHKGConstructedSliceContinuation

/-! Continuation identity/composition on composing actual domains, and
independence from unobservable extensions of a local field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG
attribute [local instance] Classical.propDecidable

theorem scalar_continuation_matching_same (a : Parameters) (state other : CurvedScalarUseState a)
    (same : ScalarUseSame a state other) (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) :
    scalarContinuationDataMatch a state request ↔ scalarContinuationDataMatch a other request := by
  have traces (x : KGSpatialSpace) (hx : x ∈ centralLeafDomain (conformalFrequency a)) :
      state.field (affineCauchyPoint request.time request.scale x) = other.field (affineCauchyPoint request.time request.scale x) ∧
      actualNormalDerivative (conformalFrequency a) state.field (affineCauchyPoint request.time request.scale x) =
        actualNormalDerivative (conformalFrequency a) other.field (affineCauchyPoint request.time request.scale x) := by
    have pointInside := inside (affine_cauchy_point_inside _ _ _ nonzero x hx)
    exact ⟨same.2 pointInside, scalar_normal_derivative_local _ _ _ _ same.2 _ pointInside⟩
  constructor
  · intro matching x hx
    exact ⟨(matching x hx).1.trans (traces x hx).1, (matching x hx).2.trans (traces x hx).2⟩
  · intro matching x hx
    exact ⟨(matching x hx).1.trans (traces x hx).1.symm, (matching x hx).2.trans (traces x hx).2.symm⟩

def ScalarContinuationOutcomeSame (a : Parameters) :
    Except ScalarContinuationFailure (CurvedScalarUseState a) →
      Except ScalarContinuationFailure (CurvedScalarUseState a) → Prop
  | .error e, .error f => e = f
  | .ok state, .ok other => ScalarUseSame a state other
  | _, _ => False

theorem scalar_continue_same (a : Parameters) (state other : CurvedScalarUseState a)
    (same : ScalarUseSame a state other) (request : ScalarContinuationRequest) :
    ScalarContinuationOutcomeSame a (scalarContinue a state request) (scalarContinue a other request) := by
  by_cases zero : request.scale = 0
  · simp [scalarContinue, zero, ScalarContinuationOutcomeSame]
  · by_cases inside : scalarContinuationDomain a request ≤ state.domain
    · have insideOther : scalarContinuationDomain a request ≤ other.domain := by rw [← same.1]; exact inside
      have matchingSame := scalar_continuation_matching_same a state other same request zero inside
      by_cases matching : scalarContinuationDataMatch a state request
      · have matchingOther := matchingSame.mp matching
        simp only [scalarContinue, zero, if_false, dif_pos inside, dif_pos insideOther,
          matching, matchingOther, if_true, ScalarContinuationOutcomeSame]
        exact ⟨rfl, fun _ _ => rfl⟩
      · have mismatchingOther : ¬ scalarContinuationDataMatch a other request := fun h => matching (matchingSame.mpr h)
        simp [scalarContinue, zero, inside, insideOther, matching, mismatchingOther, ScalarContinuationOutcomeSame]
    · have outsideOther : ¬ scalarContinuationDomain a request ≤ other.domain := by rw [← same.1]; exact inside
      simp [scalarContinue, zero, inside, outsideOther, ScalarContinuationOutcomeSame]

theorem continued_state_composition (a : Parameters) (state : CurvedScalarUseState a)
    (first : ScalarContinuationRequest) (nonzeroFirst : first.scale ≠ 0)
    (insideFirst : scalarContinuationDomain a first ≤ state.domain)
    (matchingFirst : scalarContinuationDataMatch a state first)
    (second : ScalarContinuationRequest) (nonzeroSecond : second.scale ≠ 0)
    (insideSecond : scalarContinuationDomain a second ≤ scalarContinuationDomain a first)
    (matchingSecond : scalarContinuationDataMatch a (continuedCurvedScalarState a state first insideFirst) second) :
    ScalarUseSame a
      (continuedCurvedScalarState a (continuedCurvedScalarState a state first insideFirst) second insideSecond)
      (restrictCurvedScalarUseState a state (scalarContinuationDomain a second) (insideSecond.trans insideFirst)) := by
  refine ⟨rfl, ?_⟩
  intro p hp
  exact (continued_state_agrees a _ second nonzeroSecond insideSecond matchingSecond hp).trans
    (continued_state_agrees a state first nonzeroFirst insideFirst matchingFirst (insideSecond hp))

theorem zero_unit_continuation_domain (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    scalarContinuationDomain a (evaluatedScalarContinuation a f h 0 1) =
      (initialCurvedScalarUseState a f h).domain := by
  apply Opens.ext
  ext p
  change timeAffineMap (-(0 : ℝ) / 1) (1 : ℝ)⁻¹ p ∈ protectedDiamond (conformalFrequency a) ↔ _
  have identity : timeAffineMap (-(0 : ℝ) / 1) (1 : ℝ)⁻¹ p = p := by
    funext c
    simp [time_affine_coordinate]
  rw [identity]
  rfl

theorem evaluated_continuation_identity (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) :
    ∃ result : CurvedScalarUseState a,
      scalarContinue a (initialCurvedScalarUseState a f h) (evaluatedScalarContinuation a f h 0 1) = .ok result ∧
      ScalarUseSame a result (initialCurvedScalarUseState a f h) := by
  have domains := zero_unit_continuation_domain a f h
  have inside : scalarContinuationDomain a (evaluatedScalarContinuation a f h 0 1) ≤
      (initialCurvedScalarUseState a f h).domain := le_of_eq domains
  have matching := evaluated_scalar_continuation_matches a f h 0 1
  refine ⟨continuedCurvedScalarState a _ _ inside,
    scalar_continue_success a _ _ (by norm_num [evaluatedScalarContinuation]) inside matching, domains, ?_⟩
  exact continued_state_agrees a _ _ (by norm_num [evaluatedScalarContinuation]) inside matching

end AASCKleinGordon.CurvedKG
