import KGOriginalMetricUseSemantics

/-! Canonical licensing for the actual current KG/EH metric-use contract.
Original execution failures stay negative answers; their reports remain truthful.
The current metric operand has its independently proved analytic admission.
No field contains an Einstein/Schrödinger conclusion, safety, or a license. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

structure OriginalMetricUseMeaning where
  parameters : Parameters
  geometricCoupling : ℝ
  homogeneousCoefficient : ℝ
  action : MetricSourceProbe Ω → ℝ
  originalProfiles : RestrictedRawHistory a Ω → List (PreparedHistoryOperation a Ω) → RawMetricUseReadout a s Ω
  redescriptions : RestrictedRawHistory a Ω → RestrictedRawHistory a Ω → Prop
  continuation : RestrictedRawHistory a Ω → List (PreparedHistoryOperation a Ω) → RestrictedRawHistory a Ω

def originalMetricUseMeaning (κ Λ : ℝ) : OriginalMetricUseMeaning a s Ω :=
  ⟨a, κ, Λ, originalEHRelativeAction κ Λ wickNativeFlatMetric,
    rawMetricUseProfile a s Ω κ Λ, RestrictedRawProgramSame a s Ω, restrictedRawHistoryAppend a Ω⟩

abbrev OriginalMetricUseGround := List (PreparedHistoryOperation a Ω) → RawMetricUseReadout a s Ω

def originalMetricUseAnswer (κ Λ : ℝ) (ground : OriginalMetricUseGround a s Ω) :
    (q : Unit ⊕ List (PreparedHistoryOperation a Ω)) →
      ProfileValue (fun _ => RawMetricUseReadout a s Ω) (OriginalMetricUseMeaning a s Ω) q → Prop
  | .inl _ => fun meaning => meaning = originalMetricUseMeaning a s Ω κ Λ
  | .inr ops => fun value => value = ground ops

theorem raw_first_failure_retained (h : RestrictedRawHistory a Ω)
    (ops : List (PreparedHistoryOperation a Ω)) (n : ℕ) (reason : KGExecutionFailure)
    (failed : restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω h).events = some (n, reason)) :
    restrictedRawFirstFailure a s Ω
      (restrictedRawHistoryRun a Ω (restrictedRawHistoryAppend a Ω h ops)).events = some (n, reason) := by
  rw [restricted_original_failure_readback] at failed ⊢
  rw [restrictedRawHistoryReceive, restricted_raw_history_append_present,
    ← prepared_history_continuation_square]
  exact prepared_history_quotient_first_failure_retained a s Ω ops _ n reason failed

def originalContinuationWarrant (κ Λ : ℝ) (h : RestrictedRawHistory a Ω)
    (ops : List (PreparedHistoryOperation a Ω)) (k : RestrictedRawHistory a Ω) : Prop :=
  k = restrictedRawHistoryAppend a Ω h ops ∧
    restrictedRawHistoryRun a Ω k = restrictedRawRun a Ω ops (restrictedRawHistoryRun a Ω h) ∧
    (∀ tail, rawMetricUseProfile a s Ω κ Λ k tail = rawMetricUseProfile a s Ω κ Λ h (ops ++ tail)) ∧
    (∀ n reason, restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω h).events = some (n, reason) →
      restrictedRawFirstFailure a s Ω (restrictedRawHistoryRun a Ω k).events = some (n, reason))

def originalMetricTask (κ Λ : ℝ) :
    OriginalMetricTask (RestrictedRawHistory a Ω) (RestrictedRawHistory a Ω)
      (OriginalMetricUseGround a s Ω) (OriginalMetricUseMeaning a s Ω) Unit
      (List (PreparedHistoryOperation a Ω)) (List (PreparedHistoryOperation a Ω))
      (fun _ => RawMetricUseReadout a s Ω) (RestrictedRawHistory a Ω)
      (OriginalMetricUseMeaning a s Ω) (OriginalMetricUseMeaning a s Ω) (OriginalMetricUseGround a s Ω) where
  act := id
  ground := rawMetricUseProfile a s Ω κ Λ
  descriptor := fun _ => originalMetricUseMeaning a s Ω κ Λ
  descriptorMeaning := id
  answers := rawMetricUseProfile a s Ω κ Λ
  qualification := fun ground witness => rawMetricUseProfile a s Ω κ Λ witness = ground ∧ rawHistoryQualified a s Ω witness
  originalAnswer := originalMetricUseAnswer a s Ω κ Λ
  originalLocal := fun h => OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric (restrictedRawHistoryRun a Ω h).current.act.val
  redescription := RestrictedRawProgramSame a s Ω
  redEdge := fun h _ k => RestrictedRawProgramSame a s Ω h k
  contEdge := fun h ops k => k = restrictedRawHistoryAppend a Ω h ops
  redOriginalWarrant := fun h _ k => RestrictedRawProgramSame a s Ω h k
  contOriginalWarrant := originalContinuationWarrant a s Ω κ Λ
  context := fun _ => originalMetricUseMeaning a s Ω κ Λ
  boundaryWork := id

theorem original_metric_answers_determinate (κ Λ : ℝ) :
    DependentConservation.Determinate (originalMetricTask a s Ω κ Λ).originalAnswer := by
  intro ground q x y hx hy
  cases q with
  | inl _ => exact hx.trans hy.symm
  | inr _ => exact hx.trans hy.symm

theorem every_original_history_passes_local_tests (κ Λ : ℝ) (coupling : κ ≠ 0)
    (h : RestrictedRawHistory a Ω) : originalLocalTest (originalMetricTask a s Ω κ Λ) h := by
  refine ⟨⟨h, rfl, raw_history_qualified a s Ω h⟩, ?_,
    raw_history_actual_eh_use_admitted a Ω κ Λ coupling h, ?_⟩
  · intro q
    cases q <;> rfl
  · intro k same
    exact ⟨(), k, same, rfl⟩

theorem original_history_region_postfixed (κ Λ : ℝ) (coupling : κ ≠ 0) :
    (Set.univ : Set (RestrictedRawHistory a Ω)) ⊆
      originalSafetyOperator (originalMetricTask a s Ω κ Λ) Set.univ := by
  intro h _
  refine ⟨every_original_history_passes_local_tests a s Ω κ Λ coupling h, ?_⟩
  intro t k edge
  cases t with
  | inl u =>
    exact ⟨⟨edge, ((raw_metric_use_profile_same_iff a s Ω κ Λ h k).mpr edge).symm⟩, Set.mem_univ _⟩
  | inr ops =>
    change k = restrictedRawHistoryAppend a Ω h ops at edge
    subst k
    exact ⟨⟨rfl, raw_history_append_run a Ω h ops, raw_metric_use_profile_append a s Ω κ Λ h ops,
      raw_first_failure_retained a s Ω h ops⟩, Set.mem_univ _⟩

theorem every_original_history_has_canonical_license (κ Λ : ℝ) (coupling : κ ≠ 0)
    (h : RestrictedRawHistory a Ω) :
    constructedLicensing (originalMetricTask a s Ω κ Λ) h (originalMetricUseMeaning a s Ω κ Λ) :=
  canonical_licensing_contains_every_original_sound_region _ Set.univ
    (original_history_region_postfixed a s Ω κ Λ coupling) h (Set.mem_univ h)

theorem current_metric_use_constructs_kernel_and_canonical_license (κ Λ : ℝ) (coupling : κ ≠ 0) :
    let D := originalMetricTask a s Ω κ Λ
    AASC.Instances.KernelPaper.Manuscript.DerivedKernelRoles
      (ObjecthoodNecessity.canonicalRegime (originalIncidence D)) ∧
    AASCAMetricMetricUse.AMetricLicensingDiscipline ∧
    FiveLicensingConclusions D ∧
    (∀ h, constructedLicensing D h (originalMetricUseMeaning a s Ω κ Λ)) := by
  have assembly := kernel_ametric_canonical_metric_licensing (originalMetricTask a s Ω κ Λ)
    (original_metric_answers_determinate a s Ω κ Λ)
    ⟨rawMetricUseProfile a s Ω κ Λ (initialRawHistory a Ω), initialRawHistory a Ω,
      rfl, raw_history_qualified a s Ω _⟩
  exact ⟨assembly.1, assembly.2.2.1, assembly.2.2.2.2.2,
    every_original_history_has_canonical_license a s Ω κ Λ coupling⟩

end AASCKleinGordon.CanonicalLicensing
