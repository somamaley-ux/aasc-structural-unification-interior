import KGJointFrameProjections

/-! The baseline source of the SAME original preparation under simultaneous
frame transport. This is the original Minkowski KG source; the metric act is
retained separately and does not define a new curved-background source T[gH]. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace AASCKleinGordon
open KGQuantum W9 TopologicalSpace AASCSemanticExhaustion
attribute [local instance] KGInnerCarrier.normed KGInnerCarrier.innerSpace

def kgJointFrameBaselineResponse (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricUse s Ω D (kgOriginalObject a)) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  kgInteriorFirstResponse a s Ω (kgPreparedOriginalRecord a s Ω D x)

def kgJointFrameBaselineTensor (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricUse s Ω D (kgOriginalObject a)) :
    SymmetricSourceComponents Ω :=
  wickRoleQg a s Ω (kgPreparedOriginalAttachment a s Ω D x)

theorem kg_joint_frame_original_ray_record (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (r : PhysicalRay (fockCoreDomain a)) :
    kgInteriorOriginalRay a s Ω (kgOriginalQuantumRecord a s Ω r)=kgOriginalQuantumToRay a r := by
  induction r using Quotient.inductionOn with | _ u => rfl

theorem kg_joint_frame_response_ray (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricUse s Ω D (kgOriginalObject a)) :
    kgJointFrameBaselineResponse a s Ω D x=
      originalWickRayMetricResponse a s Ω
        (kgOriginalQuantumToRay a (kgPreparedQuantum s Ω D (kgOriginalObject a) x)) := by
  unfold kgJointFrameBaselineResponse kgPreparedOriginalRecord
  rw [← kg_interior_same_first_receiver,kg_interior_first_response_at_original_ray,
    kg_joint_frame_original_ray_record]

theorem kg_joint_frame_source_all_tests (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω (kgOriginalObject a))
    (H : MetricSourceProbe Ω) :
    kgJointFrameBaselineResponse a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q x)
      (wickNativeAffineMetricTest q.left.toAdd q.right H)=
      kgJointFrameBaselineResponse a s Ω (wickOriginalMetricNeighborhood Ω) x H := by
  rw [kg_joint_frame_response_ray,kg_joint_frame_response_ray,kg_joint_frame_quantum]
  change originalWickRayMetricResponse a s (KGJointFrameRegion q Ω)
    (kgOriginalQuantumToRay a (unitaryRayMap (kgCorePoincareIsometry a q)
      (kgPreparedQuantum s Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a) x)))
    (wickNativeAffineMetricTest q.left.toAdd q.right H)=_
  rw [kg_original_quantum_ray_continuation]
  exact wick_original_ray_source_poincare a q.left.toAdd q.right s Ω _ H

theorem kg_joint_frame_baseline_half_response (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (D : Set (MetricSourceProbe Ω)) (x : KGPreparedMetricUse s Ω D (kgOriginalObject a)) :
    kgSourceHalfResponse (kgJointFrameBaselineTensor a s Ω D x)=
      kgJointFrameBaselineResponse a s Ω D x := by
  ext H
  exact (kg_source_half_response_apply _ H).trans (kg_prepared_original_all_first_tests a s Ω D x H)

theorem kg_joint_frame_source_inverse_tests (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω (kgOriginalObject a)) :
    kgJointFrameBaselineResponse a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q x)=
      (kgJointFrameBaselineResponse a s Ω (wickOriginalMetricNeighborhood Ω) x).comp
        (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω) := by
  ext J
  have same := kg_joint_frame_source_all_tests a s Ω q x
    (wickNativeAffineMetricInverseCLM q.left.toAdd q.right Ω J)
  rw [wick_native_affine_inverse_right] at same
  exact same

attribute [local irreducible] kgJointFrameBaselineResponse kgJointFrameBaselineTensor

theorem kg_joint_frame_source_tensor (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω (kgOriginalObject a)) :
    kgJointFrameBaselineTensor a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q x)=
      kgMetricSourceTransport q Ω
        (kgJointFrameBaselineTensor a s Ω (wickOriginalMetricNeighborhood Ω) x) := by
  apply kg_metric_source_transport_unique q Ω
    (kgJointFrameBaselineTensor a s Ω (wickOriginalMetricNeighborhood Ω) x)
    (kgJointFrameBaselineTensor a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q x))
  intro J
  have same := congrArg (fun f : MetricSourceProbe (KGJointFrameRegion q Ω) →L[ℝ] ℝ => f J)
    (kg_joint_frame_source_inverse_tests a s Ω q x)
  rw [← kg_joint_frame_baseline_half_response,← kg_joint_frame_baseline_half_response] at same
  exact (kg_source_half_response_apply _ J).symm.trans
    (same.trans (kg_source_half_response_apply _ _))

theorem kg_joint_frame_full_attachment_raw (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform)
    (x : KGPreparedMetricRaw Ω (wickOriginalMetricNeighborhood Ω) (kgOriginalObject a)) :
    kgPreparedOriginalAttachment a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q (Quotient.mk _ x))=
      wickRolePiA a s (KGJointFrameRegion q Ω)
        (wickOriginalRoleSource a s (KGJointFrameRegion q Ω)
          ((kgRawOriginalEquiv a).symm (kgFamilyFlow q x.preparation))) := by
  exact kg_prepared_original_attachment_raw a s (KGJointFrameRegion q Ω)
    (KGJointFrameDomain q Ω) (kgJointFrameRawEquiv Ω (kgOriginalObject a) q x)

theorem kg_joint_frame_source_ledger (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (q : ProperPoincareTransform) (x : KGJointFrameOriginal s Ω (kgOriginalObject a)) :
    kgPreparedOriginalSourceLedger a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFramePreparedEquiv s Ω (kgOriginalObject a) q x)=
      wickOriginalSourceLedgerValue (KGJointFrameRegion q Ω) :=
  kg_prepared_original_source_ledger_exact a s _ _ _

def kgJointFrameTestChange (p q : ProperPoincareTransform) (Ω : Opens CoordinatePoint) :
    MetricSourceProbe (KGJointFrameRegion p Ω) ≃L[ℝ] MetricSourceProbe (KGJointFrameRegion q Ω) :=
  (wickNativeAffineMetricTestCLE p.left.toAdd p.right Ω).symm.trans
    (wickNativeAffineMetricTestCLE q.left.toAdd q.right Ω)

theorem kg_joint_frame_test_change_value (p q : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe (KGJointFrameRegion p Ω)) :
    kgJointFrameTestChange p q Ω H=wickNativeAffineMetricTest q.left.toAdd q.right
      (wickNativeAffineMetricInverseCLM p.left.toAdd p.right Ω H) :=
  congrFun (wick_native_affine_clm_eq q.left.toAdd q.right Ω) _

theorem kg_joint_frame_test_change_identity (p : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe (KGJointFrameRegion p Ω)) :
    kgJointFrameTestChange p p Ω H=H :=
  (wickNativeAffineMetricTestCLE p.left.toAdd p.right Ω).apply_symm_apply H

theorem kg_joint_frame_test_change_composition (p q r : ProperPoincareTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe (KGJointFrameRegion p Ω)) :
    kgJointFrameTestChange q r Ω (kgJointFrameTestChange p q Ω H)=
      kgJointFrameTestChange p r Ω H := by
  change (wickNativeAffineMetricTestCLE r.left.toAdd r.right Ω)
    ((wickNativeAffineMetricTestCLE q.left.toAdd q.right Ω).symm
      ((wickNativeAffineMetricTestCLE q.left.toAdd q.right Ω)
        ((wickNativeAffineMetricTestCLE p.left.toAdd p.right Ω).symm H)))=_
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem kg_joint_frame_change_source_all_tests (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (p q : ProperPoincareTransform) (x : KGJointFrameUse s Ω (kgOriginalObject a) p)
    (H : MetricSourceProbe (KGJointFrameRegion p Ω)) :
    kgJointFrameBaselineResponse a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFrameChange s Ω (kgOriginalObject a) p q x) (kgJointFrameTestChange p q Ω H)=
      kgJointFrameBaselineResponse a s (KGJointFrameRegion p Ω) (KGJointFrameDomain p Ω) x H := by
  rw [kg_joint_frame_test_change_value]
  have left := kg_joint_frame_source_all_tests a s Ω q
    ((kgJointFramePreparedEquiv s Ω (kgOriginalObject a) p).symm x)
    (wickNativeAffineMetricInverseCLM p.left.toAdd p.right Ω H)
  have right := congrArg (fun f : MetricSourceProbe (KGJointFrameRegion p Ω) →L[ℝ] ℝ => f H)
    (kg_joint_frame_source_inverse_tests a s Ω p
      ((kgJointFramePreparedEquiv s Ω (kgOriginalObject a) p).symm x))
  rw [Equiv.apply_symm_apply] at right
  exact left.trans right.symm

theorem kg_joint_frame_change_source_ledger (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (p q : ProperPoincareTransform) (x : KGJointFrameUse s Ω (kgOriginalObject a) p) :
    kgPreparedOriginalSourceLedger a s (KGJointFrameRegion q Ω) (KGJointFrameDomain q Ω)
      (kgJointFrameChange s Ω (kgOriginalObject a) p q x)=
      wickOriginalSourceLedgerValue (KGJointFrameRegion q Ω) :=
  kg_prepared_original_source_ledger_exact a s _ _ _

end AASCKleinGordon
