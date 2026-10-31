import OriginalEHJointFrameAttachment

/-! Concrete original prepared-protocol data. Queries and failure reasons are
the existing registered ones. No new standing predicate or desired agreement
field is received. The finite-request guard is the independently existing
original metric-act domain, not the later EH domain. This is the constructed
original KG prepared branch, not every occupant of the gravity role. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

abbrev PreparedOriginal := OriginalEHPreparedUse s Ω (kgOriginalObject a)
abbrev PreparedLocus := KGJointFrameLocus s Ω (kgOriginalObject a)
abbrev PreparedQuestion := KGJointFrameQuestion Ω (kgOriginalObject a)

def preparedOriginalBase (x : PreparedLocus a s Ω) : PreparedOriginal a s Ω :=
  originalEHJointFrameOriginal s Ω (kgOriginalObject a) x

def preparedOriginalInFrame (q : ProperPoincareTransform) (z : PreparedOriginal a s Ω) :
    PreparedLocus a s Ω := ⟨q,kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q z⟩

theorem prepared_original_base_in_frame (q : ProperPoincareTransform)
    (z : PreparedOriginal a s Ω) :
    preparedOriginalBase a s Ω (preparedOriginalInFrame a s Ω q z) = z :=
  (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q).symm_apply_apply z

theorem prepared_original_in_frame_base (x : PreparedLocus a s Ω) :
    preparedOriginalInFrame a s Ω x.1 (preparedOriginalBase a s Ω x) = x := by
  obtain ⟨q,x⟩ := x
  apply congrArg (Sigma.mk q)
  exact (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q).apply_symm_apply x

theorem prepared_original_base_frame_change (q : ProperPoincareTransform)
    (x : PreparedLocus a s Ω) :
    preparedOriginalBase a s Ω (kgJointFrameLocusChange s Ω (kgOriginalObject a) q x) =
      preparedOriginalBase a s Ω x := by
  change (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q).symm
    ((kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q)
      ((kgJointFramePreparedEquiv s Ω (kgOriginalObject a) x.1).symm x.2)) = _
  exact Equiv.symm_apply_apply _ _

/-- An event stores original source and actual question. Values and diagnostics
are computed; arbitrary purported answer/standing fields cannot be supplied. -/
structure PreparedEvent where
  origin : PreparedOriginal a s Ω
  question : PreparedQuestion a Ω

def preparedEventRaw (e : PreparedEvent a s Ω) : KGPreparedReadout :=
  match e.question with
  | .inl (p,ℓ) => .inl (ℓ (kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) e.origin p))
  | .inr (.execution π) => .inr (kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) e.origin π)
  | .inr (.ledger π) => .inr (kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) e.origin π)

def preparedEventFailure (e : PreparedEvent a s Ω) : Option KGExecutionFailure :=
  match e.question with
  | .inr (.execution π) => kgExecutionFailureOf
      (kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) e.origin π)
  | _ => none

def preparedEventAnswer (e : PreparedEvent a s Ω) : Option KGPreparedReadout :=
  kgJointFrameOriginalAnswer s Ω (kgOriginalObject a) e.origin e.question

theorem prepared_event_answer_guard (e : PreparedEvent a s Ω) :
    preparedEventAnswer a s Ω e =
      if preparedEventFailure a s Ω e = none then some (preparedEventRaw a s Ω e) else none := by
  classical
  obtain ⟨z,π⟩ := e
  cases π with
  | inl test => rfl
  | inr π =>
    cases π with
    | ledger π =>
      induction z using Quotient.inductionOn with | _ z => rfl
    | execution π =>
      induction z using Quotient.inductionOn with
      | _ z =>
        change (if kgFamilySuccess (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
          (kgOriginalObject a) z.preparation π) then some _ else none) = _
        by_cases h : kgFamilySuccess (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
          (kgOriginalObject a) z.preparation π)
        · simp only [if_pos h]
          exact (if_pos h).symm
        · simp only [if_neg h]
          exact (if_neg h).symm

theorem prepared_event_failure_exact (e : PreparedEvent a s Ω) :
    preparedEventAnswer a s Ω e = none ↔ preparedEventFailure a s Ω e ≠ none := by
  classical
  rw [prepared_event_answer_guard]
  split <;> simp_all

theorem prepared_event_answer_at_frame (x : PreparedLocus a s Ω) (π : PreparedQuestion a Ω) :
    preparedEventAnswer a s Ω ⟨preparedOriginalBase a s Ω x,π⟩ =
      (kgJointFrameFamilyReferences s Ω (kgOriginalObject a)).referenceAt x π := by
  have h := kg_joint_frame_answer_original s Ω (kgOriginalObject a) x.1
    (preparedOriginalBase a s Ω x) π
  simpa only [preparedOriginalBase,originalEHJointFrameOriginal,Equiv.apply_symm_apply] using h.symm

def preparedFiniteRequest (H : MetricSourceProbe Ω) : PreparedQuestion a Ω :=
  .inr (.execution (.original .original (.original (.metric (.finite H)))))

theorem prepared_finite_request_failure (z : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω) :
    preparedEventFailure a s Ω ⟨z,preparedFiniteRequest a Ω H⟩ =
      if H ∈ wickOriginalMetricNeighborhood Ω then none else some .originalMetricRejection := by
  classical
  induction z using Quotient.inductionOn with
  | _ z =>
    change kgExecutionFailureOf (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) z.preparation (.original .original (.original (.metric (.finite H))))) = _
    change kgExecutionFailureOf (.extraction (kgConditionalValue
      (kgExtractionMap (KGExtraction.original (a := a))).toLinearMap
      (fun u => kgRawChartOutput a s Ω (wickOriginalMetricNeighborhood Ω) u
        (.original (.metric (.finite H)))) z.preparation)) = _
    rw [kg_extraction_original_map,kg_conditional_value_id]
    by_cases inside : H ∈ wickOriginalMetricNeighborhood Ω
    · simp only [kgRawChartOutput,wickChartMetricPathOutput,wickChartOriginalRoleOutput,
        if_pos inside,kgExecutionFailureOf]
    · simp only [kgRawChartOutput,wickChartMetricPathOutput,wickChartOriginalRoleOutput,
        if_neg inside,kgExecutionFailureOf]

theorem prepared_finite_request_admission_exact (z : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω) :
    (∃ v,preparedEventAnswer a s Ω ⟨z,preparedFiniteRequest a Ω H⟩ = some v) ↔
      H ∈ wickOriginalMetricNeighborhood Ω := by
  classical
  rw [prepared_event_answer_guard,prepared_finite_request_failure]
  split <;> simp_all

def preparedReplaceAct (z : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) : PreparedOriginal a s Ω :=
  kgPreparedUseOfRayAct s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) ⟨H,inside⟩
    (kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z)

theorem prepared_replace_actual_operand (z : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    (originalEHPreparedAct s Ω (kgOriginalObject a) (preparedReplaceAct a s Ω z H inside)).val = H := by
  induction z using Quotient.inductionOn with | _ z => rfl

theorem prepared_replace_quantum (z : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z H inside) =
      kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z := by
  induction z using Quotient.inductionOn with | _ z => rfl

theorem prepared_replace_original_record (z : PreparedOriginal a s Ω) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (preparedReplaceAct a s Ω z H inside) =
      kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) z := by
  induction z using Quotient.inductionOn with | _ z => rfl

theorem prepared_replace_twice (z : PreparedOriginal a s Ω) (H K : MetricSourceProbe Ω)
    (hH : H ∈ wickOriginalMetricNeighborhood Ω) (hK : K ∈ wickOriginalMetricNeighborhood Ω) :
    preparedReplaceAct a s Ω (preparedReplaceAct a s Ω z H hH) K hK =
      preparedReplaceAct a s Ω z K hK := by
  induction z using Quotient.inductionOn with | _ z => rfl

theorem prepared_replace_original (z : PreparedOriginal a s Ω) :
    preparedReplaceAct a s Ω z (originalEHPreparedAct s Ω (kgOriginalObject a) z).val
      (originalEHPreparedAct s Ω (kgOriginalObject a) z).property = z := by
  induction z using Quotient.inductionOn with | _ z => cases z;rfl

end
end AASCKleinGordon
