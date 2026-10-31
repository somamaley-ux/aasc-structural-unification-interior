import KGLicensedEHFailure
import KGLicensedScalarReceiver

/-! The common-source square is an actual original preparation, not shared
module identities or a claim that the two complete receiving quotients coincide.
The scalar source is the already declared invariant original one-particle core.
Every admitted metric operand is retained independently alongside that source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

def scalarBaseObject : KGNRObject a := ⟨.kg⟩

def scalarPreparedHistory (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) : RestrictedRawHistory a Ω :=
  ⟨1, ⟨licensedScalarOriginalPure a s Ω (scalarBaseObject a) r, H⟩, []⟩

def scalarToLicensedMetric (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    LicensedMetricReceiver a s Ω κ Λ :=
  presentLicensedHistory a s Ω κ Λ coupling (scalarPreparedHistory a s Ω r H)

theorem common_original_preparation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω (scalarToLicensedMetric a s Ω κ Λ coupling r H))) =
      rayMap _ (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r) := by
  change kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
    (restrictedEHPrepared a s Ω (Quotient.mk _ (scalarPreparedHistory a s Ω r H))) = _
  rw [restricted_eh_raw_current]
  rfl

theorem common_original_metric_operand_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    restrictedEHMetric a s Ω (licensedEHResponse a s Ω (scalarToLicensedMetric a s Ω κ Λ coupling r H)) =
      originalEHActMetric H.val := by
  change originalEHPreparedMetric s Ω (kgOriginalObject a)
    (restrictedEHPrepared a s Ω (Quotient.mk _ (scalarPreparedHistory a s Ω r H))) = _
  rw [restricted_eh_raw_current]
  rfl

theorem common_original_metric_source_record_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω})
    (q : KGFamilyQuestion a Ω (kgOriginalObject a)) :
    kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
      (restrictedEHPrepared a s Ω (licensedEHResponse a s Ω
        (scalarToLicensedMetric a s Ω κ Λ coupling r H))) (kgFamilyQuestionInChart q) =
      licensedScalarOutput a s Ω (scalarBaseObject a) r (kgNROldQuestion q) := by
  rw [licensed_scalar_old_complete_record]
  change kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)
    (restrictedEHPrepared a s Ω (Quotient.mk _ (scalarPreparedHistory a s Ω r H))) _ = _
  rw [restricted_eh_raw_current]
  exact kg_family_original_chart_exact a s Ω (kgOriginalObject a) _ q

theorem common_original_registered_reference_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω})
    (q : RegisteredQuestion (KGFamilyQuestion a Ω (kgOriginalObject a))) :
    (licensedReadout a s Ω (scalarToLicensedMetric a s Ω κ Λ coupling r H) []).answer
      (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q)) =
      (licensedScalarReference a s Ω (scalarBaseObject a) r (mapRegisteredQuestion kgNROldQuestion q)).map Sum.inr := by
  rw [licensed_readout_square a s Ω κ Λ coupling, raw_metric_use_profile_empty,
    licensed_scalar_old_reference_square]
  change restrictedRawAnswer a s Ω
    (scalarPreparedHistory a s Ω r H).initial (.inr (mapRegisteredQuestion kgFamilyQuestionInChart q)) = _
  cases q with
  | execution q =>
    change (if kgFamilySuccess (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r)
        (kgFamilyQuestionInChart q)) then some (Sum.inr (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r)
        (kgFamilyQuestionInChart q))) else none) = _
    rw [kg_family_original_chart_exact]
    change (if kgFamilySuccess (kgFamilyOutput a s Ω (kgOriginalObject a)
      (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r) q) then some _ else none) =
      (if kgFamilySuccess (kgFamilyOutput a s Ω (kgOriginalObject a)
        (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r) q) then some _ else none).map Sum.inr
    split <;> rfl
  | ledger q =>
    change some (Sum.inr (kgChartFamilyOutput a s Ω (wickOriginalMetricNeighborhood Ω)
      (kgOriginalObject a) (licensedScalarOriginalPure a s Ω (scalarBaseObject a) r)
        (kgFamilyQuestionInChart q))) = _
    rw [kg_family_original_chart_exact]
    rfl

end AASCKleinGordon.CanonicalLicensing
