import KGJointFramePrepared

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

theorem kg_joint_frame_metric_act {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω A) :
    kgPreparedMetricAct s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
      (kgJointFramePreparedEquiv s Ω A q x)=
      kgMetricActChartEquiv q Ω (kgPreparedMetricAct s Ω (wickOriginalMetricNeighborhood Ω) A x) := by
  induction x using Quotient.inductionOn with | _ x => rfl

theorem kg_joint_frame_quantum {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω A) :
    kgPreparedQuantum s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
      (kgJointFramePreparedEquiv s Ω A q x)=
      kgStandingFlow q A (kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) A x) := by
  induction x using Quotient.inductionOn with | _ x => rfl

theorem kg_joint_frame_metric_field {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω A)
    (p : Spacetime) :
    kgPreparedMetricField s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
      (kgJointFramePreparedEquiv s Ω A q x) (q.left.toAdd+spacetimeLorentzCLE q.right p)=
      (wickLorentzMatrix q.right⁻¹).transpose*
        kgPreparedMetricField s Ω (wickOriginalMetricNeighborhood Ω) A x p*
        wickLorentzMatrix q.right⁻¹ := by
  induction x using Quotient.inductionOn with
  | _ x => exact wick_native_affine_finite_metric q.left.toAdd q.right x.act.val p

theorem kg_joint_frame_complete_record {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω A)
    (π : KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) A) :
    kgPreparedCompleteRecord s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
      (kgJointFramePreparedEquiv s Ω A q x) (kgChartFamilyQuestionFrame a q π)=
      kgPreparedCompleteRecord s Ω (wickOriginalMetricNeighborhood Ω) A x π := by
  induction x using Quotient.inductionOn with
  | _ x => exact kg_chart_family_frame a s q Ω (wickOriginalMetricNeighborhood Ω) A x.preparation π

theorem kg_joint_frame_registered_reference {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω A)
    (π : RegisteredQuestion (KGChartFamilyQuestion a Ω (wickOriginalMetricNeighborhood Ω) A)) :
    (kgPreparedReferences s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A).referenceAt
      (kgJointFramePreparedEquiv s Ω A q x)
      (.inr (mapRegisteredQuestion (kgChartFamilyQuestionFrame a q) π))=
      (kgPreparedReferences s Ω (wickOriginalMetricNeighborhood Ω) A).referenceAt x (.inr π) := by
  classical
  induction x using Quotient.inductionOn with
  | _ x =>
    cases π with
    | execution π =>
      exact congrArg (fun v : KGFamilyReadout =>
        if kgFamilySuccess v then some (Sum.inr v : KGPreparedReadout) else none)
        (kg_joint_frame_complete_record s Ω A q (Quotient.mk _ x) π)
    | ledger π =>
      exact congrArg (fun v : KGFamilyReadout => some (Sum.inr v : KGPreparedReadout))
        (kg_joint_frame_complete_record s Ω A q (Quotient.mk _ x) π)

theorem kg_joint_frame_change_raw {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q : ProperPoincareTransform)
    (x : KGPreparedMetricRaw (KGJointFrameRegion p Ω) (KGJointFrameDomain p Ω) A) :
    kgJointFrameChange s Ω A p q (Quotient.mk _ x)=
      Quotient.mk _ (KGPreparedMetricRaw.mk
        (PureVector.mapUnitary (kgFrameCarrierArrow a A p q) x.preparation)
        (kgMetricActChartChange p q Ω x.act)) := rfl

theorem kg_joint_frame_change_metric {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q : ProperPoincareTransform) (x : KGJointFrameUse s Ω A p)
    (z : Spacetime) :
    kgPreparedMetricField s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
        (kgJointFrameChange s Ω A p q x) (q.left.toAdd+spacetimeLorentzCLE q.right z)=
      (wickLorentzMatrix q.right⁻¹).transpose*
        ((wickLorentzMatrix p.right).transpose*
          kgPreparedMetricField s (KGJointFrameRegion p Ω) (KGJointFrameDomain p Ω) A x
            (p.left.toAdd+spacetimeLorentzCLE p.right z)*wickLorentzMatrix p.right)*
        wickLorentzMatrix q.right⁻¹ := by
  induction x using Quotient.inductionOn with
  | _ x => exact kg_metric_act_chart_field_transition p q Ω x.act z

theorem kg_joint_frame_change_quantum {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q : ProperPoincareTransform) (x : KGJointFrameUse s Ω A p) :
    kgPreparedQuantum s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
        (kgJointFrameChange s Ω A p q x)=
      unitaryRayMap (kgFrameCarrierArrow a A p q)
        (kgPreparedQuantum s (KGJointFrameRegion p Ω) (KGJointFrameDomain p Ω) A x) := by
  induction x using Quotient.inductionOn with | _ x => rfl

end AASCKleinGordon
