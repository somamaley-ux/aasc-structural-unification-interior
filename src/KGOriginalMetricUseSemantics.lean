import OriginalRestrictedEHSource
import MetricityOriginalUseAssembly

/-! Original current-EH metric-use semantics before its licensing receiver.
Every raw operation and finite context is retained, including rejected attempts.
The history profile uses the earlier independently justified preparation carrier;
it does not invoke RestrictedOriginalResponse or its source quotient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
open AASCMetricityOriginalAssembly
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def rawHistoryProfile (h : RestrictedRawHistory a Ω) : PreparedHistoryProfile a s Ω :=
  let x := restrictedRawHistoryRun a Ω h
  ⟨restrictedRawReceive a s Ω x.source, restrictedRawReceive a s Ω x.current,
    x.events.map (restrictedRawEventReceive a s Ω)⟩

theorem raw_history_profile_same_iff (h k : RestrictedRawHistory a Ω) :
    rawHistoryProfile a s Ω h = rawHistoryProfile a s Ω k ↔ RestrictedRawProgramSame a s Ω h k := by
  constructor
  · intro same
    apply (restricted_raw_state_comparison_exact a s Ω _ _).mpr
    exact ⟨congrArg PreparedHistoryProfile.source same,
      congrArg PreparedHistoryProfile.target same, congrArg PreparedHistoryProfile.events same⟩
  · intro same
    obtain ⟨source, current, events⟩ := (restricted_raw_state_comparison_exact a s Ω _ _).mp same
    unfold rawHistoryProfile
    dsimp only
    rw [source, current, events]

theorem raw_history_current_act_same (h k : RestrictedRawHistory a Ω)
    (same : RestrictedRawProgramSame a s Ω h k) :
    (restrictedRawHistoryRun a Ω h).current.act = (restrictedRawHistoryRun a Ω k).current.act := by
  exact ((kg_prepared_metric_same_iff s Ω (wickOriginalMetricNeighborhood Ω)
    (kgOriginalObject a) _ _).mp same.2.1).1

structure RawMetricUseReadout where
  history : PreparedHistoryProfile a s Ω
  answer : PreparedQuestion a Ω → Option KGPreparedReadout
  failure : PreparedQuestion a Ω → Option KGExecutionFailure
  firstFailure : Option (ℕ × KGExecutionFailure)
  operand : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}
  metric : MetricField
  finiteAction : ℝ
  directionalAction : MetricSourceProbe Ω → ℝ

def rawMetricUseReadout (κ Λ : ℝ) (h : RestrictedRawHistory a Ω) : RawMetricUseReadout a s Ω :=
  let x := (restrictedRawHistoryRun a Ω h).current
  ⟨rawHistoryProfile a s Ω h, restrictedRawAnswer a s Ω x, restrictedRawFailure a s Ω x,
    restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω h).events, x.act,
    originalEHActMetric x.act.val, originalEHRelativeAction κ Λ wickNativeFlatMetric x.act.val,
    restrictedRawEHObserve a Ω κ Λ h⟩

theorem raw_metric_use_readout_same (κ Λ : ℝ) (h k : RestrictedRawHistory a Ω)
    (same : RestrictedRawProgramSame a s Ω h k) :
    rawMetricUseReadout a s Ω κ Λ h = rawMetricUseReadout a s Ω κ Λ k := by
  have profile := (raw_history_profile_same_iff a s Ω h k).mpr same
  have operand := raw_history_current_act_same a s Ω h k same
  have answer : restrictedRawAnswer a s Ω (restrictedRawHistoryRun a Ω h).current =
      restrictedRawAnswer a s Ω (restrictedRawHistoryRun a Ω k).current := by
    funext q
    exact restricted_raw_original_comparison_preserves_answers a s Ω _ _ same.2.1 q
  have failure : restrictedRawFailure a s Ω (restrictedRawHistoryRun a Ω h).current =
      restrictedRawFailure a s Ω (restrictedRawHistoryRun a Ω k).current := by
    funext q
    exact restricted_raw_original_comparison_preserves_failures a s Ω _ _ same.2.1 q
  have firstFailure : restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω h).events =
      restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω k).events := by
    rw [restricted_raw_first_failure_readback, restricted_raw_first_failure_readback,
      (restricted_raw_state_comparison_exact a s Ω _ _).mp same |>.2.2]
  have directional : restrictedRawEHObserve a Ω κ Λ h = restrictedRawEHObserve a Ω κ Λ k := by
    funext K
    exact restricted_eh_raw_comparison_preserves_observation a s Ω κ Λ h k same K
  unfold rawMetricUseReadout
  dsimp only
  rw [profile, answer, failure, firstFailure, operand, directional]

def rawMetricUseProfile (κ Λ : ℝ) (h : RestrictedRawHistory a Ω)
    (ops : List (PreparedHistoryOperation a Ω)) : RawMetricUseReadout a s Ω :=
  rawMetricUseReadout a s Ω κ Λ (restrictedRawHistoryAppend a Ω h ops)

theorem raw_metric_use_profile_same_iff (κ Λ : ℝ) (h k : RestrictedRawHistory a Ω) :
    rawMetricUseProfile a s Ω κ Λ h = rawMetricUseProfile a s Ω κ Λ k ↔
      RestrictedRawProgramSame a s Ω h k := by
  constructor
  · intro same
    have empty := congrArg RawMetricUseReadout.history (congrFun same [])
    simpa only [rawMetricUseProfile, rawMetricUseReadout, restrictedRawHistoryAppend,
      List.append_nil] using (raw_history_profile_same_iff a s Ω _ _).mp empty
  · intro same
    funext ops
    exact raw_metric_use_readout_same a s Ω κ Λ _ _
      (restricted_original_comparison_preserved_by_context a s Ω h k same ops)

theorem restricted_raw_run_append (first second : List (PreparedHistoryOperation a Ω))
    (x : RestrictedRawState a Ω) :
    restrictedRawRun a Ω (first ++ second) x =
      restrictedRawRun a Ω second (restrictedRawRun a Ω first x) := by
  induction first generalizing x with
  | nil => rfl
  | cons op rest ih => exact ih _

theorem raw_history_append_run (h : RestrictedRawHistory a Ω)
    (ops : List (PreparedHistoryOperation a Ω)) :
    restrictedRawHistoryRun a Ω (restrictedRawHistoryAppend a Ω h ops) =
      restrictedRawRun a Ω ops (restrictedRawHistoryRun a Ω h) :=
  restricted_raw_run_append a Ω h.program ops _

theorem raw_history_append_assoc (h : RestrictedRawHistory a Ω)
    (first second : List (PreparedHistoryOperation a Ω)) :
    restrictedRawHistoryAppend a Ω (restrictedRawHistoryAppend a Ω h first) second =
      restrictedRawHistoryAppend a Ω h (first ++ second) := by
  cases h
  simp only [restrictedRawHistoryAppend, List.append_assoc]

theorem raw_metric_use_profile_append (κ Λ : ℝ) (h : RestrictedRawHistory a Ω)
    (first second : List (PreparedHistoryOperation a Ω)) :
    rawMetricUseProfile a s Ω κ Λ (restrictedRawHistoryAppend a Ω h first) second =
      rawMetricUseProfile a s Ω κ Λ h (first ++ second) := by
  unfold rawMetricUseProfile
  rw [raw_history_append_assoc]

/-- Actual original incidence and operand domain; no licensing/safety facts. -/
def rawHistoryQualified (h : RestrictedRawHistory a Ω) : Prop :=
  let x := (restrictedRawHistoryRun a Ω h).current
  x.act.val ∈ wickOriginalMetricNeighborhood Ω ∧
    (kgRawRegisteredOrbit a s Ω (kgOriginalObject a)).kernel.standing x.preparation
      (.execution (.comparison x.preparation)) (.comparison (transitionProbability x.preparation x.preparation))

theorem raw_history_qualified (h : RestrictedRawHistory a Ω) : rawHistoryQualified a s Ω h :=
  ⟨(restrictedRawHistoryRun a Ω h).current.act.property,
    kg_raw_registered_probability a s Ω (kgOriginalObject a) _ _⟩

theorem raw_history_actual_eh_use_admitted (κ Λ : ℝ) (coupling : κ ≠ 0)
    (h : RestrictedRawHistory a Ω) :
    OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric (restrictedRawHistoryRun a Ω h).current.act.val :=
  original_eh_original_act_admitted κ Λ coupling _ (restrictedRawHistoryRun a Ω h).current.act.property

def initialRawHistory : RestrictedRawHistory a Ω :=
  ⟨1, ⟨kgFamilyVacuum a, ⟨0, wick_original_metric_neighborhood_zero Ω⟩⟩, []⟩

end AASCKleinGordon.CanonicalLicensing
