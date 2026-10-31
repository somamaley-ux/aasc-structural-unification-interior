import OriginalPreparedPlannedUseCorrection

/-! Computed consequences of the original prepared-use operations. The local
role is the eligibility of this original preparation's future metric requests.
These definitions add no state-standing classifier, purported physical identity,
burden certificate or response-agreement assumption. They receive the existing
prepared use and old operation domain. This is a downstream R2 component, not
generation of the premetric architecture from a metric. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def preparedProspectiveAdmission (z : PreparedOriginal a s Ω) (L : MetricSourceProbe Ω) : Prop :=
  ∃ v, preparedEventAnswer a s Ω ⟨z, preparedFiniteRequest a Ω
    ((originalEHPreparedAct s Ω (kgOriginalObject a) z).val + L)⟩ = some v

theorem prepared_prospective_admission_exact (z : PreparedOriginal a s Ω)
    (L : MetricSourceProbe Ω) :
    preparedProspectiveAdmission a s Ω z L ↔
      (originalEHPreparedAct s Ω (kgOriginalObject a) z).val + L ∈
        wickOriginalMetricNeighborhood Ω :=
  prepared_finite_request_admission_exact a s Ω z _

/-- Lost original future-use eligibility, not an additive debt or energy. -/
def preparedCapabilityLoss (before after : PreparedOriginal a s Ω) : Set (MetricSourceProbe Ω) :=
  {L | preparedProspectiveAdmission a s Ω before L ∧
    ¬ preparedProspectiveAdmission a s Ω after L}

def preparedCorrectionBoundary (z : PreparedOriginal a s Ω) : Set (MetricSourceProbe Ω) :=
  {K | preparedProspectiveAdmission a s Ω z K}

/-- A correction is admitted by the old domain and its ACTUAL output is target.
No field can assert the required output equality. -/
def preparedCorrectionDomain (target : PreparedOriginal a s Ω)
    (x : PreparedHistoryState a s Ω) : Set (MetricSourceProbe Ω) :=
  {K | K ∈ preparedCorrectionBoundary a s Ω (preparedOriginalBase a s Ω x.locus) ∧
    preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus = target}

theorem prepared_correction_boundary_actual_event (x : PreparedHistoryState a s Ω)
    (K : MetricSourceProbe Ω) :
    K ∈ preparedCorrectionBoundary a s Ω (preparedOriginalBase a s Ω x.locus) ↔
      preparedEventFailure a s Ω (preparedNextVariationEvent a s Ω K x) = none := by
  change preparedProspectiveAdmission a s Ω (preparedOriginalBase a s Ω x.locus) K ↔ _
  rw [prepared_prospective_admission_exact]
  change _ ↔ preparedEventFailure a s Ω
    ⟨_, preparedFiniteRequest a Ω _⟩ = none
  rw [prepared_finite_request_failure]
  split <;> simp_all

theorem prepared_nonzero_change_charges_lost_capability
    (K : MetricSourceProbe Ω) (nonzero : K ≠ 0) (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    (preparedCapabilityLoss a s Ω (preparedOriginalBase a s Ω x.locus)
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus)).Nonempty := by
  obtain ⟨L, left, right⟩ := prepared_metric_original_boundary_separates_translation Ω
    (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val K
    (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).property nonzero
  refine ⟨L, ?_, ?_⟩
  · exact (prepared_prospective_admission_exact a s Ω _ _).mpr left
  · rw [prepared_prospective_admission_exact, prepared_history_vary_operand a s Ω K x inside]
    exact right

theorem prepared_inverse_is_lawful_correction (K : MetricSourceProbe Ω)
    (x : PreparedHistoryState a s Ω)
    (inside : (originalEHPreparedAct s Ω (kgOriginalObject a)
      (preparedOriginalBase a s Ω x.locus)).val + K ∈ wickOriginalMetricNeighborhood Ω) :
    -K ∈ preparedCorrectionDomain a s Ω (preparedOriginalBase a s Ω x.locus)
      (preparedHistoryVary a s Ω K x) := by
  constructor
  · change preparedProspectiveAdmission a s Ω
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) (-K)
    rw [prepared_prospective_admission_exact, prepared_history_vary_operand a s Ω K x inside]
    simpa only [add_neg_cancel_right] using
      (originalEHPreparedAct s Ω (kgOriginalObject a)
        (preparedOriginalBase a s Ω x.locus)).property
  · exact prepared_history_restore_base a s Ω K x inside

theorem prepared_correction_restores_future_eligibility
    (target : PreparedOriginal a s Ω) (x : PreparedHistoryState a s Ω)
    (K : MetricSourceProbe Ω) (corrects : K ∈ preparedCorrectionDomain a s Ω target x)
    (L : MetricSourceProbe Ω) :
    preparedProspectiveAdmission a s Ω
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) L ↔
      preparedProspectiveAdmission a s Ω target L := by
  rw [corrects.2]

theorem prepared_correction_clears_current_capability_loss
    (target : PreparedOriginal a s Ω) (x : PreparedHistoryState a s Ω)
    (K : MetricSourceProbe Ω) (corrects : K ∈ preparedCorrectionDomain a s Ω target x) :
    preparedCapabilityLoss a s Ω target
      (preparedOriginalBase a s Ω (preparedHistoryVary a s Ω K x).locus) = ∅ := by
  rw [corrects.2]
  ext L
  simp [preparedCapabilityLoss]

/-- The declared future-use profile recovers only the already existing operand. -/
theorem prepared_future_eligibility_recovers_existing_operand
    (z w : PreparedOriginal a s Ω) :
    (∀ L, preparedProspectiveAdmission a s Ω z L ↔
      preparedProspectiveAdmission a s Ω w L) ↔
      (originalEHPreparedAct s Ω (kgOriginalObject a) z).val =
        (originalEHPreparedAct s Ω (kgOriginalObject a) w).val :=
  prepared_future_request_admission_recovers_actual_operand a s Ω z w

end
end AASCKleinGordon
