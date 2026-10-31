import KernelFaithfulLicensedEndpoints
import SRExactSourceRefinement
import SRNativeFlatManifoldOrbit
import SRAffineFrameFromOriginalTranslations
import SRNativeOrientedClockMetricAttachment
import SRProperClockRealization

/-! Actual occupied product source for the bounded flat operational SR branch.
The old preparation and admitted metric operand are retained independently of
the positive clock body's test-device data. A clock rebase is a change of
representative; scalar NR evolution is a different source operation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace AASCKleinGordon.CanonicalLicensing.SRIntegration
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace AASCMetricConstruction
open AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

abbrev SRSpace := EuclideanSpace ℝ (Fin 3)
abbrev SREvent := ℝ × SRSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

structure JointOriginalSource where
  clock : SRNativeClockUse SRSpace
  scalar : LicensedScalarReceiver a s Ω (scalarBaseObject a)
  metric : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}

def jointOldPreparation (j : JointOriginalSource a s Ω) := (j.scalar, j.metric)

def jointClockRebase (h : ℝ) (j : JointOriginalSource a s Ω) : JointOriginalSource a s Ω :=
  {j with clock := srNativeClockUseRedescription a.mass h j.clock}

def jointScalarContinue (t : ℝ) (j : JointOriginalSource a s Ω) : JointOriginalSource a s Ω :=
  {j with scalar := licensedScalarContinue a s Ω (scalarBaseObject a) t j.scalar}

def jointClockExtend (δ : ℝ) (j : JointOriginalSource a s Ω) : JointOriginalSource a s Ω :=
  {j with clock := AASCMetricConstruction.SRIntegration.srNativeExtendClockUse a.mass δ j.clock}

inductive JointOperation
  | clockRebase : ℝ → JointOperation
  | scalarContinue : ℝ → JointOperation
  | clockExtend : ℝ → JointOperation
  | certifyClockInterval : JointOperation

def jointOperation (op : JointOperation) (j : JointOriginalSource a s Ω) :
    Option (JointOriginalSource a s Ω) :=
  match op with
  | .clockRebase h => some (jointClockRebase a s Ω h j)
  | .scalarContinue t => some (jointScalarContinue a s Ω t j)
  | .clockExtend δ => if 0 ≤ δ then some (jointClockExtend a s Ω δ j) else none
  | .certifyClockInterval => if srNativeClockUseValid a.mass j.clock then some j else none

abbrev JointQuestion := ℝ ⊕ (Unit ⊕ Unit)

def jointValue : JointQuestion → Type
  | .inl _ => Fin 2 × SRNativeClockState SRSpace
  | .inr (.inl _) => LicensedScalarReceiver a s Ω (scalarBaseObject a) ×
      {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}
  | .inr (.inr _) => ℝ × ℝ × ℝ

def jointOriginalObserve (j : JointOriginalSource a s Ω) : (q : JointQuestion) → jointValue a s Ω q
  | .inl t => srNativeCoastingMarkedRecord a.mass j.clock.record t
  | .inr (.inl _) => jointOldPreparation a s Ω j
  | .inr (.inr _) => (j.clock.start,j.clock.finish,j.clock.claimed)

abbrev jointCompleteObserve :=
  srCompleteOriginalContextObserve (jointOriginalObserve a s Ω) (jointOperation a s Ω)

abbrev JointReceiver := ContextualQuotient.CanonicalQuotient (jointCompleteObserve a s Ω)

def presentJointOriginal := ContextualQuotient.classify (jointCompleteObserve a s Ω)

theorem joint_original_receiver_coverage : Function.Surjective (presentJointOriginal a s Ω) :=
  ContextualQuotient.classify_surjective _

theorem joint_all_marked_clock_records_recovered (j : JointOriginalSource a s Ω) (t : ℝ) :
    ContextualQuotient.readCoordinate (jointCompleteObserve a s Ω) (.original (.inl t))
      (presentJointOriginal a s Ω j) = srNativeCoastingMarkedRecord a.mass j.clock.record t := rfl

def jointReceiverOldPreparation : JointReceiver a s Ω →
    LicensedScalarReceiver a s Ω (scalarBaseObject a) ×
      {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω} :=
  ContextualQuotient.readCoordinate (jointCompleteObserve a s Ω) (.original (.inr (.inl ())))

theorem joint_old_preparation_square (j : JointOriginalSource a s Ω) :
    jointReceiverOldPreparation a s Ω (presentJointOriginal a s Ω j) =
      (j.scalar,j.metric) := rfl

theorem joint_interval_declaration_recovered (j : JointOriginalSource a s Ω) :
    ContextualQuotient.readCoordinate (jointCompleteObserve a s Ω)
      (.original (.inr (.inr ()))) (presentJointOriginal a s Ω j) =
        (j.clock.start,j.clock.finish,j.clock.claimed) := rfl

theorem joint_certification_has_exact_original_domain (j : JointOriginalSource a s Ω) :
    (jointOperation a s Ω .certifyClockInterval j).isSome = true ↔
      srNativeClockUseValid a.mass j.clock := by
  simp [jointOperation]

theorem joint_registered_operations_have_unique_exact_descent (op : JointOperation) :
    ∃! reduced : JointReceiver a s Ω → Option (JointReceiver a s Ω),
      ∀ j, reduced (presentJointOriginal a s Ω j) =
        Option.map (presentJointOriginal a s Ω) (jointOperation a s Ω op j) :=
  sr_registered_partial_operation_has_unique_exact_context_descent
    (jointOriginalObserve a s Ω) (jointOperation a s Ω) op

theorem joint_invalid_clock_attempt_is_retained (j : JointOriginalSource a s Ω)
    (invalid : ¬ srNativeClockUseValid a.mass j.clock) :
    jointCompleteObserve a s Ω j (.domain .certifyClockInterval) = false ∧
      jointCompleteObserve a s Ω j (.after .certifyClockInterval (.original (.inr (.inl ())))) = none := by
  simp [jointCompleteObserve,srCompleteOriginalContextObserve,jointOperation,invalid]

theorem joint_clock_rebase_preserves_all_marked_records (h t : ℝ) (j : JointOriginalSource a s Ω) :
    jointOriginalObserve a s Ω (jointClockRebase a s Ω h j) (.inl t) =
      jointOriginalObserve a s Ω j (.inl t) :=
  sr_native_clock_redescription_preserves_every_original_marked_record a.mass h j.clock.record t

theorem joint_clock_rebase_preserves_validity (h : ℝ) (j : JointOriginalSource a s Ω) :
    srNativeClockUseValid a.mass (jointClockRebase a s Ω h j).clock ↔
      srNativeClockUseValid a.mass j.clock :=
  sr_native_clock_original_use_domain_and_answer_preserved a.mass h j.clock

theorem joint_scalar_continuation_square (t : ℝ) (j : JointOriginalSource a s Ω) :
    (jointScalarContinue a s Ω t j).scalar =
      licensedScalarContinue a s Ω (scalarBaseObject a) t j.scalar := rfl

theorem joint_scalar_continuation_clock_square (t σ : ℝ) (j : JointOriginalSource a s Ω) :
    jointOriginalObserve a s Ω (jointScalarContinue a s Ω t j) (.inl σ) =
      jointOriginalObserve a s Ω j (.inl σ) := rfl

theorem joint_source_covers_every_old_preparation
    (r : LicensedScalarReceiver a s Ω (scalarBaseObject a))
    (H : {H : MetricSourceProbe Ω // H ∈ wickOriginalMetricNeighborhood Ω}) :
    ∃ j : JointOriginalSource a s Ω, srNativeClockUseValid a.mass j.clock ∧
      jointReceiverOldPreparation a s Ω (presentJointOriginal a s Ω j) = (r,H) := by
  obtain ⟨c,hc⟩ := sr_native_physical_rest_duration_safe_region_is_nonempty
    (E:=SRSpace) a.mass a.mass_pos
  exact ⟨⟨c,r,H⟩,(sr_native_clock_greatest_original_safe_region_computed a.mass c).mp hc,rfl⟩

def jointToLicensedMetric (κ Λ : ℝ) (coupling : κ ≠ 0) (j : JointReceiver a s Ω) :=
  scalarToLicensedMetric a s Ω κ Λ coupling
    (jointReceiverOldPreparation a s Ω j).1 (jointReceiverOldPreparation a s Ω j).2

theorem joint_to_eh_original_preparation_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (j : JointOriginalSource a s Ω) :
    jointToLicensedMetric a s Ω κ Λ coupling (presentJointOriginal a s Ω j) =
      scalarToLicensedMetric a s Ω κ Λ coupling j.scalar j.metric := rfl

theorem joint_to_eh_metric_operand_square (κ Λ : ℝ) (coupling : κ ≠ 0)
    (j : JointOriginalSource a s Ω) :
    restrictedEHMetric a s Ω (licensedEHResponse a s Ω
      (jointToLicensedMetric a s Ω κ Λ coupling (presentJointOriginal a s Ω j))) =
      originalEHActMetric j.metric.val :=
  common_original_metric_operand_square a s Ω κ Λ coupling j.scalar j.metric

end AASCKleinGordon.CanonicalLicensing.SRIntegration
