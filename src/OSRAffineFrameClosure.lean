import OSRAffineFrames

noncomputable section
set_option autoImplicit false
open Set AASCMetricConstruction AASCMetricConstruction.SRIntegration AASCSemanticExhaustion
open AASCKleinGordon.CanonicalLicensing.SRIntegration
namespace AASCKleinGordon.OperationalSR

theorem actual_affine_identity (p : SREvent) : frameEvent 1 0 p=p := by
  simp [frameEvent,sr_event_frame_one]

def actualAffineHomeomorph (A : SRMatrixFrame) (b : SREvent) : SREvent ≃ₜ SREvent where
  toFun := frameEvent A b
  invFun := frameInverse A b
  left_inv := frame_inverse_left A b
  right_inv := frame_inverse_right A b
  continuous_toFun := (srMatrixFrameEvent A).continuous_toFun.add continuous_const
  continuous_invFun := (srMatrixFrameEvent A⁻¹).continuous_toFun.comp (continuous_id.sub continuous_const)

theorem actual_affine_open_domain_transport (A : SRMatrixFrame) (b : SREvent) (O : Set SREvent) (openDomain : IsOpen O) :
    IsOpen (frameEvent A b '' O) := (actualAffineHomeomorph A b).isOpenMap O openDomain

theorem actual_affine_inverse_is_the_inverse_frame (A : SRMatrixFrame) (b p : SREvent) :
    frameInverse A b p=frameEvent A⁻¹ (-srMatrixFrameEventLinear A⁻¹ b) p := by
  simp [frameInverse,frameEvent,map_sub,sub_eq_add_neg]

end AASCKleinGordon.OperationalSR
