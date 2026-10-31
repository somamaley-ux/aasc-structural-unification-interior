import KGPreparedOriginalSource
import KGMetricActFieldTransitions
import KGMetricActChartReadouts

/-! Simultaneous prepared-use transport. Both operands are transported from
one original raw preparation and one declared admitted metric act. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

abbrev KGJointFrameRegion (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :=
  wickAffineMetricRegion q.left.toAdd q.right Ω

abbrev KGJointFrameDomain (q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :=
  wickTransportedMetricDomain q.left.toAdd q.right Ω

abbrev KGJointFrameOriginal {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) := KGPreparedMetricUse s Ω (wickOriginalMetricNeighborhood Ω) A

abbrev KGJointFrameUse {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) :=
  KGPreparedMetricUse s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A

def kgJointFramePureEquiv {a : Parameters} (A : KGFamilyObject a)
    (q : ProperPoincareTransform) : PureVector (KGFamilyCarrier A) ≃ PureVector (KGFamilyCarrier A) where
  toFun := kgFamilyFlow q
  invFun := PureVector.mapUnitary (kgComparisonPoincare a q A.shape).symm
  left_inv x := Subtype.ext ((kgComparisonPoincare a q A.shape).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((kgComparisonPoincare a q A.shape).apply_symm_apply x.val)

def kgJointFrameRawEquiv {a : Parameters} (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) :
    KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) A ≃
      KGPreparedMetricRaw (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A where
  toFun x := ⟨kgFamilyFlow q x.preparation,kgMetricActChartEquiv q Ω x.act⟩
  invFun x := ⟨(kgJointFramePureEquiv A q).symm x.preparation,
    (kgMetricActChartEquiv q Ω).symm x.act⟩
  left_inv x := by
    cases x
    change KGPreparedMetricRaw.mk
      ((kgJointFramePureEquiv A q).symm ((kgJointFramePureEquiv A q) _))
      ((kgMetricActChartEquiv q Ω).symm ((kgMetricActChartEquiv q Ω) _))=_
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  right_inv x := by
    cases x
    change KGPreparedMetricRaw.mk
      ((kgJointFramePureEquiv A q) ((kgJointFramePureEquiv A q).symm _))
      ((kgMetricActChartEquiv q Ω) ((kgMetricActChartEquiv q Ω).symm _))=_
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]

def kgJointFrameRayEquiv {a : Parameters} (A : KGFamilyObject a)
    (q : ProperPoincareTransform) : PhysicalRay (KGFamilyCarrier A) ≃ PhysicalRay (KGFamilyCarrier A) where
  toFun := unitaryRayMap (kgComparisonPoincare a q A.shape)
  invFun := unitaryRayMap (kgComparisonPoincare a q A.shape).symm
  left_inv r := by
    induction r using Quotient.inductionOn with
    | _ x =>
      change rayMap _ ((kgJointFramePureEquiv A q).symm ((kgJointFramePureEquiv A q) x))=rayMap _ x
      rw [Equiv.symm_apply_apply]
  right_inv r := by
    induction r using Quotient.inductionOn with
    | _ x =>
      change rayMap _ ((kgJointFramePureEquiv A q) ((kgJointFramePureEquiv A q).symm x))=rayMap _ x
      rw [Equiv.apply_symm_apply]

theorem kg_joint_frame_raw_same {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x y : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) A) :
    kgPreparedMetricSame s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω) A
      (kgJointFrameRawEquiv Ω A q x) (kgJointFrameRawEquiv Ω A q y) ↔
      kgPreparedMetricSame s Ω (wickOriginalMetricNeighborhood Ω) A x y := by
  rw [kg_prepared_metric_same_iff,kg_prepared_metric_same_iff]
  change ((kgMetricActChartEquiv q Ω) x.act=(kgMetricActChartEquiv q Ω) y.act ∧
    (kgJointFrameRayEquiv A q) (rayMap _ x.preparation)=
      (kgJointFrameRayEquiv A q) (rayMap _ y.preparation)) ↔ _
  rw [(kgMetricActChartEquiv q Ω).injective.eq_iff,
    (kgJointFrameRayEquiv A q).injective.eq_iff]

def kgJointFramePreparedEquiv {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform) :
    KGJointFrameOriginal s Ω A ≃ KGJointFrameUse s Ω A q where
  toFun := Quotient.map (kgJointFrameRawEquiv Ω A q)
    (fun x y same => (kg_joint_frame_raw_same s Ω A q x y).mpr same)
  invFun := Quotient.map (kgJointFrameRawEquiv Ω A q).symm (by
    intro x y same
    apply (kg_joint_frame_raw_same s Ω A q _ _).mp
    simpa only [Equiv.apply_symm_apply] using same)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ ((kgJointFrameRawEquiv Ω A q).symm ((kgJointFrameRawEquiv Ω A q) x))=_
      rw [Equiv.symm_apply_apply]
  right_inv x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      change Quotient.mk _ ((kgJointFrameRawEquiv Ω A q) ((kgJointFrameRawEquiv Ω A q).symm x))=_
      rw [Equiv.apply_symm_apply]

theorem kg_joint_frame_prepared_raw_square {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (q : ProperPoincareTransform)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) A) :
    kgJointFramePreparedEquiv s Ω A q (Quotient.mk _ x)=
      Quotient.mk _ (KGPreparedMetricRaw.mk (kgFamilyFlow q x.preparation)
        (kgMetricActChartEquiv q Ω x.act)) := rfl

def kgJointFrameChange {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q : ProperPoincareTransform) :
    KGJointFrameUse s Ω A p ≃ KGJointFrameUse s Ω A q :=
  (kgJointFramePreparedEquiv s Ω A p).symm.trans (kgJointFramePreparedEquiv s Ω A q)

theorem kg_joint_frame_change_identity {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p : ProperPoincareTransform) (x : KGJointFrameUse s Ω A p) :
    kgJointFrameChange s Ω A p p x=x := (kgJointFramePreparedEquiv s Ω A p).apply_symm_apply x

theorem kg_joint_frame_change_composition {a : Parameters} (s : ℝ) (Ω : Opens CoordinatePoint)
    (A : KGFamilyObject a) (p q r : ProperPoincareTransform) (x : KGJointFrameUse s Ω A p) :
    kgJointFrameChange s Ω A q r (kgJointFrameChange s Ω A p q x)=kgJointFrameChange s Ω A p r x := by
  change (kgJointFramePreparedEquiv s Ω A r)
    ((kgJointFramePreparedEquiv s Ω A q).symm ((kgJointFramePreparedEquiv s Ω A q)
      ((kgJointFramePreparedEquiv s Ω A p).symm x)))=_
  rw [Equiv.symm_apply_apply]
  rfl

end AASCKleinGordon
