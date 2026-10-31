import OriginalR2ExecutionRefinement

/-! The independently existing original KG prequotient preparation source.
Raw answers are evaluated from the actual preparation and metric operand,
not by calling the receiving quotient. This is the fixed KG source/program
restriction, not a definition of the full abstract R2 operative source. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

abbrev RestrictedRaw := KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)

def restrictedRawReceive (x : RestrictedRaw a Ω) : PreparedOriginal a s Ω := Quotient.mk _ x

def RestrictedRawSame (x y : RestrictedRaw a Ω) : Prop :=
  kgPreparedMetricSame s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) x y

theorem restricted_raw_receive_eq_iff (x y : RestrictedRaw a Ω) :
    restrictedRawReceive a s Ω x = restrictedRawReceive a s Ω y ↔ RestrictedRawSame a s Ω x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

def restrictedRawAnswer (x : RestrictedRaw a Ω) : PreparedQuestion a Ω → Option KGPreparedReadout
  | .inl (p, l) => some (.inl (l (wickOriginalFiniteMetric x.act.val p)))
  | .inr (.execution π) =>
      if kgFamilySuccess (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
        (kgOriginalObject a) x.preparation π) then
        some (.inr (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
          (kgOriginalObject a) x.preparation π)) else none
  | .inr (.ledger π) => some (.inr (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) x.preparation π))

def restrictedRawFailure (x : RestrictedRaw a Ω) : PreparedQuestion a Ω → Option KGExecutionFailure
  | .inr (.execution π) => kgExecutionFailureOf
      (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
        (kgOriginalObject a) x.preparation π)
  | _ => none

theorem restricted_raw_answer_square (x : RestrictedRaw a Ω) (π : PreparedQuestion a Ω) :
    restrictedRawAnswer a s Ω x π =
      preparedEventAnswer a s Ω ⟨restrictedRawReceive a s Ω x, π⟩ := by
  cases π with
  | inl _ => rfl
  | inr π => cases π <;> rfl

theorem restricted_raw_failure_square (x : RestrictedRaw a Ω) (π : PreparedQuestion a Ω) :
    restrictedRawFailure a s Ω x π =
      preparedEventFailure a s Ω ⟨restrictedRawReceive a s Ω x, π⟩ := by
  cases π with
  | inl _ => rfl
  | inr π => cases π <;> rfl

theorem restricted_raw_admission_exact (x : RestrictedRaw a Ω) (π : PreparedQuestion a Ω) :
    (∃ v, restrictedRawAnswer a s Ω x π = some v) ↔
      ∃ v, preparedEventAnswer a s Ω ⟨restrictedRawReceive a s Ω x, π⟩ = some v := by
  rw [restricted_raw_answer_square]

theorem restricted_raw_original_comparison_preserves_answers
    (x y : RestrictedRaw a Ω) (same : RestrictedRawSame a s Ω x y) (π : PreparedQuestion a Ω) :
    restrictedRawAnswer a s Ω x π = restrictedRawAnswer a s Ω y π := by
  rw [restricted_raw_answer_square, restricted_raw_answer_square,
    (restricted_raw_receive_eq_iff a s Ω x y).mpr same]

theorem restricted_raw_original_comparison_preserves_failures
    (x y : RestrictedRaw a Ω) (same : RestrictedRawSame a s Ω x y) (π : PreparedQuestion a Ω) :
    restrictedRawFailure a s Ω x π = restrictedRawFailure a s Ω y π := by
  rw [restricted_raw_failure_square, restricted_raw_failure_square,
    (restricted_raw_receive_eq_iff a s Ω x y).mpr same]

theorem restricted_raw_unrestricted_attempt_guard (x : RestrictedRaw a Ω) (H : MetricSourceProbe Ω) :
    restrictedRawFailure a s Ω x (preparedFiniteRequest a Ω H) =
      if H ∈ wickOriginalMetricNeighborhood Ω then none else some .originalMetricRejection := by
  rw [restricted_raw_failure_square, prepared_finite_request_failure]

def restrictedRawReplace (x : RestrictedRaw a Ω) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) : RestrictedRaw a Ω :=
  ⟨x.preparation, ⟨H, inside⟩⟩

theorem restricted_raw_replace_square (x : RestrictedRaw a Ω) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    restrictedRawReceive a s Ω (restrictedRawReplace a Ω x H inside) =
      preparedReplaceAct a s Ω (restrictedRawReceive a s Ω x) H inside := by
  cases x
  rfl

/-- Existing structured source, with the actual preparation as shared operand. -/
def restrictedRawNativeSource (x : RestrictedRaw a Ω) :=
  wickOriginalRoleSource a s Ω ((kgRawOriginalEquiv a).symm x.preparation)

theorem restricted_raw_native_attachment_readback (x : RestrictedRaw a Ω) :
    kgPreparedOriginalAttachment a s Ω (wickOriginalMetricNeighborhood Ω)
      (restrictedRawReceive a s Ω x) =
      wickRolePiA a s Ω (restrictedRawNativeSource a s Ω x) :=
  kg_prepared_original_attachment_raw a s Ω (wickOriginalMetricNeighborhood Ω) x

structure RestrictedRawEvent where
  origin : RestrictedRaw a Ω
  question : PreparedQuestion a Ω

def restrictedRawEventReceive (e : RestrictedRawEvent a Ω) : PreparedEvent a s Ω :=
  ⟨restrictedRawReceive a s Ω e.origin, e.question⟩

def RestrictedRawEventSame (e f : RestrictedRawEvent a Ω) : Prop :=
  RestrictedRawSame a s Ω e.origin f.origin ∧ e.question = f.question

theorem restricted_raw_event_comparison_exact (e f : RestrictedRawEvent a Ω) :
    restrictedRawEventReceive a s Ω e = restrictedRawEventReceive a s Ω f ↔
      RestrictedRawEventSame a s Ω e f := by
  constructor
  · intro same
    exact ⟨(restricted_raw_receive_eq_iff a s Ω _ _).mp
      (congrArg PreparedEvent.origin same), congrArg PreparedEvent.question same⟩
  · rintro ⟨same, question⟩
    cases e with
    | mk x π =>
      cases f with
      | mk y ρ =>
        have origins := (restricted_raw_receive_eq_iff a s Ω x y).mpr same
        change π = ρ at question
        change PreparedEvent.mk (restrictedRawReceive a s Ω x) π =
          PreparedEvent.mk (restrictedRawReceive a s Ω y) ρ
        rw [origins, question]

end
end AASCKleinGordon
