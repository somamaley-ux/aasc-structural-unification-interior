import KGCanonicalMetricLicensing
import OriginalRestrictedEHKernelReceiving

/-! Actual receiver maps from the canonical license's retained original content.
The complete licensing receiver retains the original act and every profile.
Metric/history readouts are taken there, never asserted on the coarser EH source
quotient. Every old raw history and source profile is covered. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace MeasureTheory
open AASC.KernelReference AASCMetricityOriginalAssembly AASCMetricityLicensingConstruction
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

abbrev LicensedMetricReceiver (κ Λ : ℝ) :=
  let D := originalMetricTask a s Ω κ Λ
  CanonicalLicensingReceiver D.act D.descriptor D.answers
    (originalLocalTest D) (declaredOriginalEdge D) (originalEdgeTest D)

theorem original_history_is_safe (κ Λ : ℝ) (coupling : κ ≠ 0) (h : RestrictedRawHistory a Ω) :
    h ∈ canonicalSafeUses (originalMetricTask a s Ω κ Λ) :=
  original_sound_region_is_safe _ _ _ Set.univ
    (original_history_region_postfixed a s Ω κ Λ coupling) h (Set.mem_univ h)

def presentLicensedHistory (κ Λ : ℝ) (coupling : κ ≠ 0) (h : RestrictedRawHistory a Ω) :
    LicensedMetricReceiver a s Ω κ Λ :=
  presentSafeOriginalUse (originalMetricTask a s Ω κ Λ).act
    (originalMetricTask a s Ω κ Λ).descriptor (originalMetricTask a s Ω κ Λ).answers
    (originalLocalTest (originalMetricTask a s Ω κ Λ))
    (declaredOriginalEdge (originalMetricTask a s Ω κ Λ))
    (originalEdgeTest (originalMetricTask a s Ω κ Λ))
    ⟨h, original_history_is_safe a s Ω κ Λ coupling h⟩

def licensedHistory {κ Λ : ℝ} (r : LicensedMetricReceiver a s Ω κ Λ) : RestrictedRawHistory a Ω :=
  (r.val ()).1.1

def licensedReadout {κ Λ : ℝ} (r : LicensedMetricReceiver a s Ω κ Λ)
    (ops : List (PreparedHistoryOperation a Ω)) : RawMetricUseReadout a s Ω := (r.val ()).2 ops

theorem raw_metric_use_profile_empty (κ Λ : ℝ) (h : RestrictedRawHistory a Ω) :
    rawMetricUseProfile a s Ω κ Λ h [] = rawMetricUseReadout a s Ω κ Λ h := by
  unfold rawMetricUseProfile
  congr 1
  cases h
  simp only [restrictedRawHistoryAppend, List.append_nil]

theorem licensed_history_present (κ Λ : ℝ) (coupling : κ ≠ 0) (h : RestrictedRawHistory a Ω) :
    licensedHistory a s Ω (presentLicensedHistory a s Ω κ Λ coupling h) = h := rfl

theorem present_licensed_history_surjective (κ Λ : ℝ) (coupling : κ ≠ 0) :
    Function.Surjective (presentLicensedHistory a s Ω κ Λ coupling) := by
  intro r
  obtain ⟨c, hc⟩ := r.property
  exact ⟨c.val, Subtype.ext hc⟩

theorem licensed_readout_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (ops : List (PreparedHistoryOperation a Ω)) :
    licensedReadout a s Ω r ops = rawMetricUseProfile a s Ω κ Λ (licensedHistory a s Ω r) ops := by
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  rfl

theorem receiver_has_actual_canonical_license (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) :
    constructedLicensing (originalMetricTask a s Ω κ Λ) (licensedHistory a s Ω r)
      (originalMetricUseMeaning a s Ω κ Λ) :=
  every_original_history_has_canonical_license a s Ω κ Λ coupling _

def licensedEHResponse {κ Λ : ℝ} (r : LicensedMetricReceiver a s Ω κ Λ) :
    RestrictedOriginalResponse a s Ω := Quotient.mk _ (licensedHistory a s Ω r)

def licensedEHSourceProfile {κ Λ : ℝ} (r : LicensedMetricReceiver a s Ω κ Λ) :
    RestrictedEHKernelProfile a s Ω κ Λ := restrictedRawEHKernelClass a s Ω κ Λ (licensedHistory a s Ω r)

def licensedContinue (κ Λ : ℝ) (coupling : κ ≠ 0)
    (ops : List (PreparedHistoryOperation a Ω)) (r : LicensedMetricReceiver a s Ω κ Λ) :
    LicensedMetricReceiver a s Ω κ Λ :=
  presentLicensedHistory a s Ω κ Λ coupling (restrictedRawHistoryAppend a Ω (licensedHistory a s Ω r) ops)

theorem licensed_response_continuation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (ops : List (PreparedHistoryOperation a Ω)) (r : LicensedMetricReceiver a s Ω κ Λ) :
    licensedEHResponse a s Ω (licensedContinue a s Ω κ Λ coupling ops r) =
      restrictedOriginalResponseContinue a s Ω ops (licensedEHResponse a s Ω r) := rfl

theorem licensed_readout_continuation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (first second : List (PreparedHistoryOperation a Ω)) (r : LicensedMetricReceiver a s Ω κ Λ) :
    licensedReadout a s Ω (licensedContinue a s Ω κ Λ coupling first r) second =
      licensedReadout a s Ω r (first ++ second) := by
  rw [licensed_readout_square a s Ω κ Λ coupling,
    licensed_readout_square a s Ω κ Λ coupling]
  exact raw_metric_use_profile_append a s Ω κ Λ _ first second

theorem licensed_response_coverage (κ Λ : ℝ) (coupling : κ ≠ 0) :
    Function.Surjective (licensedEHResponse a s Ω (κ := κ) (Λ := Λ)) := by
  intro q
  obtain ⟨h, rfl⟩ := Quotient.exists_rep q
  exact ⟨presentLicensedHistory a s Ω κ Λ coupling h, rfl⟩

theorem licensed_source_profile_coverage (κ Λ : ℝ) (coupling : κ ≠ 0) :
    Function.Surjective (licensedEHSourceProfile a s Ω (κ := κ) (Λ := Λ)) := by
  intro q
  obtain ⟨h, same⟩ := restricted_eh_raw_kernel_coverage a s Ω κ Λ q
  exact ⟨presentLicensedHistory a s Ω κ Λ coupling h, same⟩

theorem licensed_metric_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) :
    (licensedReadout a s Ω r []).metric = restrictedEHMetric a s Ω (licensedEHResponse a s Ω r) := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty]
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  change originalEHActMetric (restrictedRawHistoryRun a Ω h).current.act.val =
    originalEHPreparedMetric s Ω (kgOriginalObject a) (restrictedEHPrepared a s Ω (Quotient.mk _ h))
  rw [restricted_eh_raw_current]
  rfl

theorem licensed_action_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) :
    (licensedReadout a s Ω r []).finiteAction =
      originalEHRelativeAction κ Λ wickNativeFlatMetric (restrictedEHAct a s Ω (licensedEHResponse a s Ω r)).val := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty]
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  change originalEHRelativeAction κ Λ wickNativeFlatMetric (restrictedRawHistoryRun a Ω h).current.act.val =
    originalEHRelativeAction κ Λ wickNativeFlatMetric
      (originalEHPreparedAct s Ω (kgOriginalObject a) (restrictedEHPrepared a s Ω (Quotient.mk _ h))).val
  rw [restricted_eh_raw_current]
  rfl

theorem licensed_directional_action_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (K : MetricSourceProbe Ω) :
    (licensedReadout a s Ω r []).directionalAction K =
      restrictedEHObserve a s Ω κ Λ (licensedEHResponse a s Ω r) K := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty]
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  exact restricted_eh_raw_observation_square a s Ω κ Λ h K

theorem licensed_original_answer_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (q : PreparedQuestion a Ω) :
    (licensedReadout a s Ω r []).answer q =
      preparedHistoryReference a s Ω (restrictedOriginalResponseReceive a s Ω (licensedEHResponse a s Ω r)) q := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty]
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  exact restricted_original_current_answer_readback a s Ω h q

theorem licensed_original_first_failure_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) :
    (licensedReadout a s Ω r []).firstFailure =
      preparedHistoryReadFirstFailure a s Ω
        (restrictedOriginalResponseReceive a s Ω (licensedEHResponse a s Ω r)) := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty]
  obtain ⟨h, rfl⟩ := present_licensed_history_surjective a s Ω κ Λ coupling r
  exact restricted_original_failure_readback a s Ω h

theorem licensed_eh_source_is_original_directional_action (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (K : MetricSourceProbe Ω) :
    (1 / 2 : ℝ) * metricSourcePairing
      (restrictedEHKernelSource a s Ω κ Λ coupling (licensedEHSourceProfile a s Ω r)) K =
        (licensedReadout a s Ω r []).directionalAction K := by
  rw [licensed_directional_action_square a s Ω κ Λ coupling]
  rw [licensedEHSourceProfile, restrictedRawEHKernelClass, restricted_eh_kernel_source_receipt]
  exact restricted_eh_source_half_pairing a s Ω κ Λ coupling _ K

theorem licensed_eh_same_metric_representation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedMetricReceiver a s Ω κ Λ) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    restrictedEHKernelSource a s Ω κ Λ coupling (licensedEHSourceProfile a s Ω r) i φ =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (licensedReadout a s Ω r []).metric
        (originalEHGeometricResponse κ Λ (licensedReadout a s Ω r []).metric)) i p * φ p := by
  rw [licensed_metric_square a s Ω κ Λ coupling]
  exact restricted_eh_kernel_same_metric_representation a s Ω κ Λ coupling _ i φ

end AASCKleinGordon.CanonicalLicensing
