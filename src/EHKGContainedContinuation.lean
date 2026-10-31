import EHKGAffineMetricUniqueness
import EHKGAffineDiamondGeometry
import EHKGFiniteScalarUse

/-! Actual continuation requests carry Schwartz Cauchy data, not an evolution
certificate. Geometry and actual position/normal traces are checked before
acceptance. The constructed restarted field is proved equal to the old local
history on the receiving domain by the same-EH uniqueness theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap Topology
namespace AASCKleinGordon.CurvedKG
attribute [local instance] Classical.propDecidable

structure ScalarContinuationRequest where
  time : ℝ
  scale : ℝ
  position : 𝓢(KGSpatialSpace, ℂ)
  velocity : 𝓢(KGSpatialSpace, ℂ)

def scalarContinuationDomain (a : Parameters) (request : ScalarContinuationRequest) : Opens CoordinatePoint :=
  ⟨affineDependenceDiamond (conformalFrequency a) request.time request.scale,
    affine_diamond_open _ _ _⟩

def scalarContinuationField (a : Parameters) (request : ScalarContinuationRequest) : CoordinatePoint → ℝ :=
  shiftedCurvedSchwartzField a request.time request.position request.velocity

def scalarContinuationDataMatch (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) : Prop :=
  ∀ x ∈ centralLeafDomain (conformalFrequency a),
    scalarContinuationField a request (affineCauchyPoint request.time request.scale x) =
        state.field (affineCauchyPoint request.time request.scale x) ∧
    actualNormalDerivative (conformalFrequency a) (scalarContinuationField a request) (affineCauchyPoint request.time request.scale x) =
        actualNormalDerivative (conformalFrequency a) state.field (affineCauchyPoint request.time request.scale x)

def continuedCurvedScalarState (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (inside : scalarContinuationDomain a request ≤ state.domain) : CurvedScalarUseState a where
  domain := scalarContinuationDomain a request
  domain_inside := fun p hp => state.domain_inside (inside hp)
  field := scalarContinuationField a request
  regular := (shifted_curved_smooth a request.time request.position request.velocity).contDiffOn
  equation := fun p hp => shifted_curved_same_eh_equation a request.time request.position request.velocity p
    (protected_diamond_subset_ball _ (state.domain_inside (inside hp)))

inductive ScalarContinuationFailure where
  | zeroScale
  | outsideDomain
  | traceMismatch
  deriving DecidableEq

def scalarContinue (a : Parameters) (state : CurvedScalarUseState a) (request : ScalarContinuationRequest) :
    Except ScalarContinuationFailure (CurvedScalarUseState a) :=
  if request.scale = 0 then .error .zeroScale
  else if inside : scalarContinuationDomain a request ≤ state.domain then
    if scalarContinuationDataMatch a state request then .ok (continuedCurvedScalarState a state request inside)
    else .error .traceMismatch
  else .error .outsideDomain

theorem continued_state_agrees (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) (matching : scalarContinuationDataMatch a state request) :
    EqOn (continuedCurvedScalarState a state request inside).field state.field (scalarContinuationDomain a request) := by
  intro p hp
  apply affine_same_eh_local_unique a request.time request.scale nonzero
    (fun q hq => state.domain_inside (inside hq)) _ _
    (continuedCurvedScalarState a state request inside).regular (state.regular.mono inside)
    (continuedCurvedScalarState a state request inside).equation
    (fun q hq => state.equation q (inside hq))
    (fun x hx => (matching x hx).1) (fun x hx => (matching x hx).2) p hp

theorem continued_state_is_restriction (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) (matching : scalarContinuationDataMatch a state request) :
    ScalarUseSame a (continuedCurvedScalarState a state request inside)
      (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) :=
  ⟨rfl, continued_state_agrees a state request nonzero inside matching⟩

theorem continuation_retains_all_finite_uses (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) (matching : scalarContinuationDataMatch a state request)
    (program : List ScalarUseOperation) :
    (scalarUseRun a (continuedCurvedScalarState a state request inside) program).2 =
        (scalarUseRun a (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) program).2 ∧
    firstScalarUseFailure (scalarUseRun a (continuedCurvedScalarState a state request inside) program).2 =
        firstScalarUseFailure (scalarUseRun a (restrictCurvedScalarUseState a state (scalarContinuationDomain a request) inside) program).2 := by
  have same := continued_state_is_restriction a state request nonzero inside matching
  exact ⟨(scalar_use_run_same a program _ _ same).2, scalar_use_first_failure_same a program _ _ same⟩

theorem scalar_continue_success (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) (matching : scalarContinuationDataMatch a state request) :
    scalarContinue a state request = .ok (continuedCurvedScalarState a state request inside) := by
  simp only [scalarContinue, nonzero, if_false, dif_pos inside, matching, if_true]

theorem scalar_continue_zero_scale_fails (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (zero : request.scale = 0) :
    scalarContinue a state request = .error .zeroScale := by simp [scalarContinue, zero]

theorem scalar_continue_outside_fails (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (outside : ¬ scalarContinuationDomain a request ≤ state.domain) :
    scalarContinue a state request = .error .outsideDomain := by simp [scalarContinue, nonzero, outside]

theorem scalar_continue_trace_mismatch_fails (a : Parameters) (state : CurvedScalarUseState a)
    (request : ScalarContinuationRequest) (nonzero : request.scale ≠ 0)
    (inside : scalarContinuationDomain a request ≤ state.domain) (mismatch : ¬ scalarContinuationDataMatch a state request) :
    scalarContinue a state request = .error .traceMismatch := by simp [scalarContinue, nonzero, inside, mismatch]

end AASCKleinGordon.CurvedKG
