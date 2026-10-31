import OSRFrameSupply

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

def frameEvent (A : SRMatrixFrame) (b p : SREvent) : SREvent := srMatrixFrameEventLinear A p+b
def frameInverse (A : SRMatrixFrame) (b p : SREvent) : SREvent := srMatrixFrameEventLinear A⁻¹ (p-b)

theorem frame_inverse_left (A : SRMatrixFrame) (b p : SREvent) :
    frameInverse A b (frameEvent A b p)=p := by
  simp only [frameEvent,frameInverse,add_sub_cancel_right]
  exact sr_event_frame_inverse_left A p

theorem frame_inverse_right (A : SRMatrixFrame) (b p : SREvent) :
    frameEvent A b (frameInverse A b p)=p := by
  unfold frameEvent frameInverse
  rw [←sr_event_frame_mul,mul_inv_cancel,sr_event_frame_one,sub_add_cancel]

theorem frame_event_injective (A : SRMatrixFrame) (b : SREvent) : Function.Injective (frameEvent A b) := by
  intro p q same
  exact (srMatrixFrameEventLinear A).injective (add_right_cancel same)

theorem frame_event_composition (A B : SRMatrixFrame) (a b p : SREvent) :
    frameEvent A a (frameEvent B b p)=frameEvent (A*B) (frameEvent A a b) p := by
  simp only [frameEvent,map_add,sr_event_frame_mul]
  abel

theorem frame_event_difference (A : SRMatrixFrame) (b p q : SREvent) :
    frameEvent A b q-frameEvent A b p=srMatrixFrameEventLinear A (q-p) := by
  simp only [frameEvent,map_sub]
  abel

theorem frame_preserves_actual_source_form (A : SRMatrixFrame) (admitted : A ∈ srNativeFrameComparisons)
    (b p q : SREvent) :
    srOriginalOrderQuadratic (frameEvent A b q-frameEvent A b p)=srOriginalOrderQuadratic (q-p) := by
  rw [frame_event_difference,sr_original_order_quadratic_computed,sr_original_order_quadratic_computed]
  exact sr_source_form_isometry_event_value A admitted.1 (q-p)

theorem frame_barycentric (A : SRMatrixFrame) (b p q : SREvent) (t : ℝ) :
    frameEvent A b ((1-t) • p+t • q)=(1-t) • frameEvent A b p+t • frameEvent A b q := by
  simp only [frameEvent,map_add,map_smul,smul_add]
  have split : b=(1-t) • b+t • b := by rw [←add_smul];simp
  conv_lhs => rw [split]
  abel

def segmentCovered (O : Set SREvent) (p q : SREvent) : Prop :=
  ∀ t ∈ Icc (0:ℝ) 1, (1-t) • p+t • q ∈ O

theorem actual_segment_domain_transport (A : SRMatrixFrame) (b p q : SREvent) (O : Set SREvent) :
    segmentCovered (frameEvent A b '' O) (frameEvent A b p) (frameEvent A b q) ↔ segmentCovered O p q := by
  constructor
  · intro covered t ht
    have point := covered t ht
    rw [←frame_barycentric] at point
    obtain ⟨x,hx,same⟩ := point
    have equal := frame_event_injective A b same
    rwa [equal] at hx
  · intro covered t ht
    rw [←frame_barycentric]
    exact ⟨_,covered t ht,rfl⟩

theorem whole_affine_segments_populated (p q : SREvent) : segmentCovered univ p q := by
  intro t ht
  trivial

end AASCKleinGordon.OperationalSR
