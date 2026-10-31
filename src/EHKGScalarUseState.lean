import EHKGAllCompactCauchy
import EHKGLocalSmoothRestriction

/-! Actual local scalar histories and point/normal observations. Domain
rejection is explicit. States are initialized by the proved Cauchy family;
equality of local histories preserves answers independently of extensions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped Topology
namespace AASCKleinGordon.CurvedKG
attribute [local instance] Classical.propDecidable

structure CurvedScalarUseState (a : Parameters) where
  domain : Opens CoordinatePoint
  domain_inside : (domain : Set CoordinatePoint) ⊆ protectedDiamond (conformalFrequency a)
  field : CoordinatePoint → ℝ
  regular : ContDiffOn ℝ (⊤ : ℕ∞) field domain
  equation : ∀ p ∈ domain,
    scalarFieldWaveOperator (originalEHActMetric (conformalOperand (conformalFrequency a))) field p =
      (massWaveNumber a) ^ 2 * field p

def initialCurvedScalarUseState (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞)) : CurvedScalarUseState a where
  domain := ⟨protectedDiamond (conformalFrequency a), protected_diamond_open _⟩
  domain_inside := Subset.rfl
  field := compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h
  regular := (compact_curved_field_smooth a _ f h).contDiffOn
  equation := fun p hp => compact_curved_field_equation a _ f h p (protected_diamond_subset_ball _ hp)

inductive CurvedScalarQuestion where
  | value (point : CoordinatePoint)
  | normal (point : CoordinatePoint)

def CurvedScalarQuestion.point : CurvedScalarQuestion → CoordinatePoint
  | .value p => p
  | .normal p => p

inductive CurvedScalarUseFailure where
  | outsideDomain
  | invalidRestriction
  | incompatibleMetric
  deriving DecidableEq

def scalarQuestionAnswer (a : Parameters) (state : CurvedScalarUseState a)
    (q : CurvedScalarQuestion) : Option ℝ :=
  if q.point ∈ state.domain then
    some (match q with
      | .value p => state.field p
      | .normal p => actualNormalDerivative (conformalFrequency a) state.field p)
  else none

def scalarQuestionFailure (a : Parameters) (state : CurvedScalarUseState a)
    (q : CurvedScalarQuestion) : Option CurvedScalarUseFailure :=
  if q.point ∈ state.domain then none else some .outsideDomain

def restrictCurvedScalarUseState (a : Parameters) (state : CurvedScalarUseState a)
    (W : Opens CoordinatePoint) (inside : W ≤ state.domain) : CurvedScalarUseState a where
  domain := W
  domain_inside := fun p hp => state.domain_inside (inside hp)
  field := state.field
  regular := state.regular.mono inside
  equation := fun p hp => state.equation p (inside hp)

def ScalarUseSame (a : Parameters) (state other : CurvedScalarUseState a) : Prop :=
  state.domain = other.domain ∧ EqOn state.field other.field state.domain

theorem scalar_normal_derivative_local (nu : ℝ) (D : Opens CoordinatePoint)
    (F G : CoordinatePoint → ℝ) (same : EqOn F G D) (p : CoordinatePoint) (inside : p ∈ D) :
    actualNormalDerivative nu F p = actualNormalDerivative nu G p := by
  have near : F =ᶠ[𝓝 p] G := by
    filter_upwards [D.isOpen.mem_nhds inside] with q hq
    exact same hq
  exact congrArg (fun L : CoordinatePoint →L[ℝ] ℝ => L (timeUnitNormal nu p)) near.fderiv_eq

theorem scalar_use_same_preserves_answers (a : Parameters) (state other : CurvedScalarUseState a)
    (same : ScalarUseSame a state other) (q : CurvedScalarQuestion) :
    scalarQuestionAnswer a state q = scalarQuestionAnswer a other q := by
  cases q with
  | value p =>
    unfold scalarQuestionAnswer CurvedScalarQuestion.point
    rw [← same.1]
    by_cases hp : p ∈ state.domain
    · simp only [hp, if_true, same.2 hp]
    · simp only [hp, if_false]
  | normal p =>
    unfold scalarQuestionAnswer CurvedScalarQuestion.point
    rw [← same.1]
    by_cases hp : p ∈ state.domain
    · simp only [hp, if_true, scalar_normal_derivative_local _ _ _ _ same.2 p hp]
    · simp only [hp, if_false]

theorem scalar_use_same_preserves_failures (a : Parameters) (state other : CurvedScalarUseState a)
    (same : ScalarUseSame a state other) (q : CurvedScalarQuestion) :
    scalarQuestionFailure a state q = scalarQuestionFailure a other q := by
  simp only [scalarQuestionFailure, same.1]

theorem scalar_question_outside_stays_failed (a : Parameters) (state : CurvedScalarUseState a)
    (q : CurvedScalarQuestion) (outside : q.point ∉ state.domain) :
    scalarQuestionAnswer a state q = none ∧ scalarQuestionFailure a state q = some .outsideDomain := by
  simp [scalarQuestionAnswer, scalarQuestionFailure, outside]

theorem initial_scalar_position_answer (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)) :
    scalarQuestionAnswer a (initialCurvedScalarUseState a f h) (.value (centralLeafPoint x)) = some (f x) := by
  have pointInside := (central_leaf_in_diamond_iff _ x).mpr inside
  change (if centralLeafPoint x ∈ protectedDiamond (conformalFrequency a) then
    some (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h (centralLeafPoint x)) else none) = some (f x)
  rw [if_pos pointInside]
  congr 1
  simpa only [central_leaf_space] using compact_curved_initial_position a _ f h (centralLeafPoint x) (central_leaf_time x)

theorem initial_scalar_normal_answer (a : Parameters)
    (f h : TestFunction (centralLeafDomain (conformalFrequency a)) ℝ (⊤ : ℕ∞))
    (x : KGSpatialSpace) (inside : x ∈ centralLeafDomain (conformalFrequency a)) :
    scalarQuestionAnswer a (initialCurvedScalarUseState a f h) (.normal (centralLeafPoint x)) = some (h x) := by
  have pointInside := (central_leaf_in_diamond_iff _ x).mpr inside
  change (if centralLeafPoint x ∈ protectedDiamond (conformalFrequency a) then
    some (actualNormalDerivative (conformalFrequency a)
      (compactCurvedField a (centralLeafDomain (conformalFrequency a)) f h) (centralLeafPoint x)) else none) = some (h x)
  rw [if_pos pointInside]
  exact congrArg some (compact_curved_initial_normal a f h x)

end AASCKleinGordon.CurvedKG
