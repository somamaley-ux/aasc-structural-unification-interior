import OriginalEHOriginalActVariation
import OriginalEHConstructedFrameTransport
import KGJointFrameReferences
import KGOriginalMultiplierBinding

/-! Attach the constructed EH readout to the existing ORIGINAL joint frame
carrier. Its operand is the old projected act. The bundled frame test supplies
the actual transport; neither an operand map nor evaluator agreement is assumed.
This covers the existing frame contexts and original multiplier comparison,
not the entire gravity AER interface or all original candidate coverage. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace

variable {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint) (A : KGFamilyObject a)

def originalEHJointFrameUse (κ Λ : ℝ) (q : ProperPoincareTransform)
    (x : KGJointFrameUse s Ω A q) :=
  originalEHFiniteUse κ Λ wickNativeFlatMetric
    (kgPreparedMetricAct s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A x).val

theorem original_eh_joint_frame_same_metric (q : ProperPoincareTransform)
    (x : KGJointFrameUse s Ω A q) (p : Spacetime) :
    originalEHActMetric
      (kgPreparedMetricAct s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A x).val
      (wickSpacetimeCoordinates p) =
      kgPreparedMetricField s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A x p := by
  rw [kg_prepared_metric_field_eq]
  rfl

theorem original_eh_joint_frame_admitted (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : ProperPoincareTransform) (x : KGJointFrameUse s Ω A q) :
    OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric
      (kgPreparedMetricAct s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A x).val :=
  original_eh_transported_original_domain κ Λ coupling q.left.toAdd q.right _
    (kgPreparedMetricAct s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A x).property

theorem original_eh_joint_frame_evaluator (κ Λ : ℝ) (q : ProperPoincareTransform)
    (x : KGJointFrameOriginal s Ω A) :
    (originalEHJointFrameUse s Ω A κ Λ q (kgJointFramePreparedEquiv s Ω A q x)).2 =
      (originalEHPreparedUse s Ω A κ Λ x).2 := by
  unfold originalEHJointFrameUse
  rw [kg_joint_frame_metric_act]
  exact original_eh_original_frame_evaluator κ Λ q.left.toAdd q.right
    (originalEHPreparedAct s Ω A x).val (originalEHPreparedAct s Ω A x).property

theorem original_eh_joint_frame_change_evaluator (κ Λ : ℝ)
    (p q : ProperPoincareTransform) (x : KGJointFrameUse s Ω A p) :
    (originalEHJointFrameUse s Ω A κ Λ q (kgJointFrameChange s Ω A p q x)).2 =
      (originalEHJointFrameUse s Ω A κ Λ p x).2 := by
  have left := original_eh_joint_frame_evaluator s Ω A κ Λ q
    ((kgJointFramePreparedEquiv s Ω A p).symm x)
  have right := original_eh_joint_frame_evaluator s Ω A κ Λ p
    ((kgJointFramePreparedEquiv s Ω A p).symm x)
  rw [Equiv.apply_symm_apply] at right
  exact left.trans right.symm

def originalEHJointFrameReferences (κ Λ : ℝ) :
    AASC.PartialReferenceSystem (KGJointFrameLocus s Ω A)
      (KGJointFrameQuestion Ω A ⊕ Unit) (KGPreparedReadout ⊕ ℝ) where
  referenceAt x q := match q with
    | .inl old => ((kgJointFrameFamilyReferences s Ω A).referenceAt x old).map Sum.inl
    | .inr _ => (originalEHJointFrameUse s Ω A κ Λ x.1 x.2).2.map Sum.inr

theorem original_eh_joint_frame_old_square (κ Λ : ℝ)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (originalEHJointFrameReferences s Ω A κ Λ).referenceAt x (.inl π) =
      ((kgJointFrameFamilyReferences s Ω A).referenceAt x π).map Sum.inl := rfl

theorem original_eh_joint_frame_reference_square (κ Λ : ℝ)
    (q : ProperPoincareTransform) (x : KGJointFrameLocus s Ω A)
    (π : KGJointFrameQuestion Ω A ⊕ Unit) :
    (originalEHJointFrameReferences s Ω A κ Λ).referenceAt (kgJointFrameLocusChange s Ω A q x) π =
      (originalEHJointFrameReferences s Ω A κ Λ).referenceAt x π := by
  cases π with
  | inl old =>
    simp only [original_eh_joint_frame_old_square,kg_joint_frame_family_reference_square]
  | inr action =>
    change Option.map Sum.inr
      (originalEHJointFrameUse s Ω A κ Λ q (kgJointFrameChange s Ω A x.1 q x.2)).2 = _
    rw [original_eh_joint_frame_change_evaluator]
    rfl

def originalEHJointFrameContinuation (κ Λ : ℝ) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A ⊕ Unit) :
    (originalEHJointFrameReferences s Ω A κ Λ).incidenceSystem.Continuation
      (x,π) (kgJointFrameLocusChange s Ω A q x,π) where
  map reference := ⟨reference.value,by
    change (originalEHJointFrameReferences s Ω A κ Λ).referenceAt _ π = some reference.value
    rw [original_eh_joint_frame_reference_square]
    exact reference.isIncident⟩

theorem original_eh_joint_frame_standing (κ Λ : ℝ) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A ⊕ Unit) :
    (originalEHJointFrameReferences s Ω A κ Λ).incidenceSystem.AdmissibleAt
      (kgJointFrameLocusChange s Ω A q x) π ↔
      (originalEHJointFrameReferences s Ω A κ Λ).incidenceSystem.AdmissibleAt x π := by
  change (∃ v,(originalEHJointFrameReferences s Ω A κ Λ).referenceAt _ π = some v) ↔
    ∃ v,(originalEHJointFrameReferences s Ω A κ Λ).referenceAt x π = some v
  rw [original_eh_joint_frame_reference_square]

theorem original_eh_joint_frame_failure (κ Λ : ℝ) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A ⊕ Unit) :
    (originalEHJointFrameReferences s Ω A κ Λ).kernel.FailureAt
      (kgJointFrameLocusChange s Ω A q x) π ↔
      (originalEHJointFrameReferences s Ω A κ Λ).kernel.FailureAt x π := by
  change (∀ v,¬ (originalEHJointFrameReferences s Ω A κ Λ).referenceAt _ π = some v) ↔
    ∀ v,¬ (originalEHJointFrameReferences s Ω A κ Λ).referenceAt x π = some v
  rw [original_eh_joint_frame_reference_square]

theorem original_eh_joint_frame_old_failure_exact (κ Λ : ℝ)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (originalEHJointFrameReferences s Ω A κ Λ).referenceAt x (.inl π) = none ↔
      (kgJointFrameFamilyReferences s Ω A).referenceAt x π = none := by
  rw [original_eh_joint_frame_old_square]
  cases (kgJointFrameFamilyReferences s Ω A).referenceAt x π <;> simp

theorem original_eh_joint_frame_old_standing_exact (κ Λ : ℝ)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A) :
    (originalEHJointFrameReferences s Ω A κ Λ).incidenceSystem.AdmissibleAt x (.inl π) ↔
      (kgJointFrameFamilyReferences s Ω A).incidenceSystem.AdmissibleAt x π := by
  change (∃ v,Option.map Sum.inl
    ((kgJointFrameFamilyReferences s Ω A).referenceAt x π) = some v) ↔
    ∃ v,(kgJointFrameFamilyReferences s Ω A).referenceAt x π = some v
  cases (kgJointFrameFamilyReferences s Ω A).referenceAt x π <;> simp

def originalEHJointFrameOriginal (x : KGJointFrameLocus s Ω A) : KGJointFrameOriginal s Ω A :=
  (kgJointFramePreparedEquiv s Ω A x.1).symm x.2

theorem original_eh_joint_frame_profile_iff_original
    (x y : KGJointFrameLocus s Ω A) :
    (∀ π,(kgJointFrameFamilyReferences s Ω A).referenceAt x π =
      (kgJointFrameFamilyReferences s Ω A).referenceAt y π) ↔
      originalEHJointFrameOriginal s Ω A x = originalEHJointFrameOriginal s Ω A y := by
  have left (π : KGJointFrameQuestion Ω A) := kg_joint_frame_answer_original s Ω A x.1
    (originalEHJointFrameOriginal s Ω A x) π
  have right (π : KGJointFrameQuestion Ω A) := kg_joint_frame_answer_original s Ω A y.1
    (originalEHJointFrameOriginal s Ω A y) π
  simp only [originalEHJointFrameOriginal,Equiv.apply_symm_apply] at left right
  constructor
  · intro same
    apply kg_joint_frame_original_profile_faithful s Ω A
    intro π
    exact (left π).symm.trans ((same π).trans (right π))
  · intro same π
    exact (left π).trans ((congrArg (fun z => kgJointFrameOriginalAnswer s Ω A z π) same).trans
      (right π).symm)

theorem original_eh_joint_frame_extended_profile_iff_old (κ Λ : ℝ)
    (x y : KGJointFrameLocus s Ω A) :
    (∀ π,(originalEHJointFrameReferences s Ω A κ Λ).referenceAt x π =
      (originalEHJointFrameReferences s Ω A κ Λ).referenceAt y π) ↔
    (∀ π,(kgJointFrameFamilyReferences s Ω A).referenceAt x π =
      (kgJointFrameFamilyReferences s Ω A).referenceAt y π) := by
  constructor
  · intro same π
    have h := same (.inl π)
    rw [original_eh_joint_frame_old_square,original_eh_joint_frame_old_square] at h
    cases hx : (kgJointFrameFamilyReferences s Ω A).referenceAt x π <;>
      cases hy : (kgJointFrameFamilyReferences s Ω A).referenceAt y π <;> simp_all
  · intro same π
    cases π with
    | inl old => simp only [original_eh_joint_frame_old_square,same old]
    | inr action =>
      have base := (original_eh_joint_frame_profile_iff_original s Ω A x y).mp same
      have left := original_eh_joint_frame_evaluator s Ω A κ Λ x.1
        (originalEHJointFrameOriginal s Ω A x)
      have right := original_eh_joint_frame_evaluator s Ω A κ Λ y.1
        (originalEHJointFrameOriginal s Ω A y)
      simp only [originalEHJointFrameOriginal,Equiv.apply_symm_apply] at left right
      change Option.map Sum.inr (originalEHJointFrameUse s Ω A κ Λ x.1 x.2).2 =
        Option.map Sum.inr (originalEHJointFrameUse s Ω A κ Λ y.1 y.2).2
      rw [left,right]
      exact congrArg (fun z => Option.map Sum.inr (originalEHPreparedUse s Ω A κ Λ z).2) base

theorem original_eh_joint_frame_no_repair (κ Λ : ℝ) (q : ProperPoincareTransform)
    (x : KGJointFrameLocus s Ω A) (π : KGJointFrameQuestion Ω A ⊕ Unit)
    (failed : (originalEHJointFrameReferences s Ω A κ Λ).kernel.FailureAt x π) :
    ¬ (originalEHJointFrameReferences s Ω A κ Λ).incidenceSystem.AdmissibleAt
      (kgJointFrameLocusChange s Ω A q x) π := by
  have none := ((originalEHJointFrameReferences s Ω A κ Λ).referenceAt_eq_none_iff x π).mpr failed
  rintro ⟨v,hv⟩
  change (originalEHJointFrameReferences s Ω A κ Λ).referenceAt _ π = some v at hv
  rw [original_eh_joint_frame_reference_square,none] at hv
  cases hv

theorem original_eh_multiplier_actual_evaluator (a : Parameters) (κ Λ : ℝ)
    (lam t : ℝ)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    (originalEHJointFrameUse s Ω (kgOriginalObject a) κ Λ (kgOriginalTimeFrame a t)
      (Quotient.mk _ (kgMultiplierPreparedRaw a Ω lam t x))).2 =
      (originalEHPreparedUse s Ω (kgOriginalObject a) κ Λ (Quotient.mk _ x)).2 := by
  rw [kg_multiplier_prepared_quotient]
  exact original_eh_joint_frame_evaluator s Ω (kgOriginalObject a) κ Λ _ _

end
end AASCKleinGordon
