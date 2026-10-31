import KGConstraintEnergyMultiplier
import KGJointFrameSource
import KGJointFrameReferences
import WickCalibratedChargeClosure

/-! The actual constraint-multiplier flow on the original common core, with
the same admitted metric operand moved by the original physical-time frame.
Its scalar phase changes no complete original reference or full source.
This is the original-law AER-P comparison component, not the full AER receiver. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace
local instance (a : Parameters) : (n : ℕ) → NormedSpace ℂ (bosonicHilbertSector a n) :=
  fun _ => inferInstance

theorem kg_original_constraint_energy_from_source (a : Parameters) (u : fockCoreDomain a) :
    (kgConstraintEnergyOperator a u).val=
      wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a) u := by
  let v := (fockCoreDomainEquiv a).symm u
  have hf : includedFockCore a v=u := (fockCoreDomainEquiv a).apply_symm_apply u
  have actual := wick_original_stress_energy_on_core a (wickPositiveCalibratedAmplitude a) v
  rw [hf,wick_positive_calibrated_amplitude_coefficient,one_smul] at actual
  have original := fockCoreEnergy_on_original_core a v
  rw [hf] at original
  change fockCoreEnergy a u=_
  exact original.trans actual.symm

theorem kg_original_h0_calibrated_source_quadratic (a : Parameters) (u : fockCoreDomain a) :
    kgConstraintEnergyH0 a u=(1/(2*a.hbar)) *
      (inner ℂ u.val (wickOriginalStressEnergyCharge a (wickPositiveCalibratedAmplitude a) u)).re := by
  change (1/(2*a.hbar)) * (inner ℂ u.val (kgConstraintEnergyOperator a u).val).re=_
  rw [kg_original_constraint_energy_from_source]

def kgOriginalTimeFrame (a : Parameters) (t : ℝ) : ProperPoincareTransform :=
  ⟨Multiplicative.ofAdd (timeTranslationEvent a t),1⟩

def kgMultiplierPreparedRaw (a : Parameters) (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    KGPreparedMetricRaw (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
      (KGJointFrameDomain (kgOriginalTimeFrame a t) Ω) (kgOriginalObject a) :=
  ⟨PureVector.smul (Translation.phase 1 t lam)
      (kg_constraint_energy_multiplier_phase_nonzero lam t)
      (PureVector.mapUnitary (kgConstraintEnergyTime a t) x.preparation),
    kgMetricActChartEquiv (kgOriginalTimeFrame a t) Ω x.act⟩

theorem kg_multiplier_prepared_actual_flow (a : Parameters)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    (kgMultiplierPreparedRaw a Ω lam t x).preparation.val =
      kgConstraintEnergyMultiplierFlow a lam t x.preparation.val := rfl

theorem kg_multiplier_prepared_same_original (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    kgPreparedMetricSame s (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
      (KGJointFrameDomain (kgOriginalTimeFrame a t) Ω) (kgOriginalObject a)
      (kgMultiplierPreparedRaw a Ω lam t x)
      (kgJointFrameRawEquiv Ω (kgOriginalObject a) (kgOriginalTimeFrame a t) x) := by
  apply (kg_prepared_metric_same_iff s _ _ _ _ _).mpr
  refine ⟨rfl,?_⟩
  change rayMap (fockCoreDomain a) (PureVector.smul (Translation.phase 1 t lam)
    (kg_constraint_energy_multiplier_phase_nonzero lam t)
    (PureVector.mapUnitary (kgConstraintEnergyTime a t)
      (x.preparation : PureVector (fockCoreDomain a)))) =
    rayMap (fockCoreDomain a) (PureVector.mapUnitary
      (kgCorePoincareIsometry a (kgOriginalTimeFrame a t))
      (x.preparation : PureVector (fockCoreDomain a)))
  rw [rayMap_smul]
  congr 1
  apply Subtype.ext
  exact kg_constraint_energy_time_original a t x.preparation.val

theorem kg_multiplier_prepared_quotient (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x) :
      KGJointFrameUse s Ω (kgOriginalObject a) (kgOriginalTimeFrame a t))=
      kgJointFramePreparedEquiv s Ω (kgOriginalObject a) (kgOriginalTimeFrame a t)
        (Quotient.mk _ x) :=
  Quotient.sound (kg_multiplier_prepared_same_original a s Ω lam t x)

theorem kg_multiplier_prepared_all_references (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a))
    (π : KGJointFrameQuestion Ω (kgOriginalObject a)) :
    kgJointFrameAnswer s Ω (kgOriginalObject a) (kgOriginalTimeFrame a t)
      (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x)) π=
      kgJointFrameOriginalAnswer s Ω (kgOriginalObject a) (Quotient.mk _ x) π := by
  rw [kg_multiplier_prepared_quotient]
  exact kg_joint_frame_answer_original s Ω (kgOriginalObject a) (kgOriginalTimeFrame a t) _ π

theorem kg_multiplier_prepared_full_source (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    kgPreparedOriginalAttachment a s (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
      (KGJointFrameDomain (kgOriginalTimeFrame a t) Ω)
      (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x))=
      wickRolePiA a s (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
        (wickOriginalRoleSource a s (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
          ((kgRawOriginalEquiv a).symm (kgFamilyFlow (kgOriginalTimeFrame a t) x.preparation))) := by
  rw [kg_multiplier_prepared_quotient]
  exact kg_joint_frame_full_attachment_raw a s Ω (kgOriginalTimeFrame a t) x

theorem kg_multiplier_prepared_all_source_tests (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a))
    (H : MetricSourceProbe Ω) :
    kgJointFrameBaselineResponse a s (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
      (KGJointFrameDomain (kgOriginalTimeFrame a t) Ω)
      (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x))
      (wickNativeAffineMetricTest (kgOriginalTimeFrame a t).left.toAdd
        (kgOriginalTimeFrame a t).right H)=
      kgJointFrameBaselineResponse a s Ω (wickOriginalMetricNeighborhood Ω) (Quotient.mk _ x) H := by
  rw [kg_multiplier_prepared_quotient]
  exact kg_joint_frame_source_all_tests a s Ω (kgOriginalTimeFrame a t) _ H

theorem kg_multiplier_prepared_failed_locus (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a))
    (π : KGJointFrameQuestion Ω (kgOriginalObject a)) :
    kgJointFrameAnswer s Ω (kgOriginalObject a) (kgOriginalTimeFrame a t)
      (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x)) π=none ↔
      kgJointFrameOriginalAnswer s Ω (kgOriginalObject a) (Quotient.mk _ x) π=none := by
  rw [kg_multiplier_prepared_all_references]

theorem kg_multiplier_calibrated_source_tests (a : Parameters)
    (Ω : Opens CoordinatePoint) (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a))
    (H : MetricSourceProbe Ω) :
    kgJointFrameBaselineResponse a (wickPositiveCalibratedAmplitude a)
      (KGJointFrameRegion (kgOriginalTimeFrame a t) Ω)
      (KGJointFrameDomain (kgOriginalTimeFrame a t) Ω)
      (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x))
      (wickNativeAffineMetricTest (kgOriginalTimeFrame a t).left.toAdd
        (kgOriginalTimeFrame a t).right H)=
      kgJointFrameBaselineResponse a (wickPositiveCalibratedAmplitude a) Ω
        (wickOriginalMetricNeighborhood Ω) (Quotient.mk _ x) H :=
  kg_multiplier_prepared_all_source_tests a (wickPositiveCalibratedAmplitude a) Ω lam t x H

end AASCKleinGordon
