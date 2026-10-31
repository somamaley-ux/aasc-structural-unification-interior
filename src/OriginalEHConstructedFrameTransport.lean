import OriginalEHMetricActGeometry
import OriginalEHAnalyticTransport
import WickNativeLFTransport

/-! Construct the transport data from the ORIGINAL bundled affine metric
test. No caller-supplied transformed test or action agreement remains on this
declared physical Poincare branch. The original frame map supplies the region,
derivative and tensor operand; the EH action/evaluator square follows. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion TopologicalSpace

variable {Ω : Opens CoordinatePoint}

theorem original_eh_inverse_affine_derivative (b : Spacetime) (L : ProperLorentzTransform)
    (p : CoordinatePoint) :
    HasFDerivAt (wickAffineCoordinateHomeomorph b L).symm
      (properLorentzFourCLE L).symm.toContinuousLinearMap p := by
  change HasFDerivAt (fun q => (properLorentzFourCLE L).symm (q-wickSpacetimeCoordinates b)) _ p
  simpa only [ContinuousLinearMap.comp_id] using
    ((properLorentzFourCLE L).symm.toContinuousLinearMap.hasFDerivAt.comp p
      ((hasFDerivAt_id p).sub_const (wickSpacetimeCoordinates b)))

theorem original_eh_inverse_affine_regular (b : Spacetime) (L : ProperLorentzTransform)
    (p : CoordinatePoint) : ContDiffAt ℝ 3 (wickAffineCoordinateHomeomorph b L).symm p :=
  ((properLorentzFourCLE L).symm.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt

theorem original_eh_inverse_affine_jacobian (b : Spacetime) (L : ProperLorentzTransform)
    (p : CoordinatePoint) :
    coordinateJacobian (wickAffineCoordinateHomeomorph b L).symm p = wickLorentzMatrix L⁻¹ := by
  ext i j
  have derivative := original_eh_inverse_affine_derivative b L p
  rw [coordinateJacobian_vector _ p derivative.differentiableAt,derivative.fderiv]
  rfl

theorem original_eh_affine_flat_pullback (b : Spacetime) (L : ProperLorentzTransform) :
    coordinateMetricPullback wickNativeFlatMetric (wickAffineCoordinateHomeomorph b L).symm =
      wickNativeFlatMetric := by
  funext p
  rw [coordinateMetricPullback_matrix,original_eh_inverse_affine_jacobian]
  exact wick_lorentz_flat_metric L⁻¹

theorem original_eh_constructed_affine_test (b : Spacetime) (L : ProperLorentzTransform)
    (H : MetricSourceProbe Ω) (p : CoordinatePoint) :
    originalEHTestTensor (wickNativeAffineMetricTest b L H p) =
      (coordinateJacobian (wickAffineCoordinateHomeomorph b L).symm p).transpose *
        originalEHTestTensor (H ((wickAffineCoordinateHomeomorph b L).symm p)) *
          coordinateJacobian (wickAffineCoordinateHomeomorph b L).symm p := by
  rw [original_eh_inverse_affine_jacobian]
  exact wick_tensor_congruence_encode (wickLorentzMatrix L⁻¹) _

def originalEHOriginalFrameTransport (b : Spacetime) (L : ProperLorentzTransform)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    EHTransportData wickNativeFlatMetric H (wickNativeAffineMetricTest b L H) where
  coordinate := (wickAffineCoordinateHomeomorph b L).symm
  region := by
    change (wickAffineCoordinateHomeomorph b L).symm ''
      ((wickAffineCoordinateHomeomorph b L) '' (Ω : Set CoordinatePoint)) = (Ω : Set CoordinatePoint)
    ext p
    constructor
    · rintro ⟨q,⟨r,hr,rfl⟩,rfl⟩
      simpa only [Homeomorph.symm_apply_apply] using hr
    · intro hp
      exact ⟨(wickAffineCoordinateHomeomorph b L) p,⟨p,hp,rfl⟩,
        (wickAffineCoordinateHomeomorph b L).symm_apply_apply p⟩
  injective := (wickAffineCoordinateHomeomorph b L).symm.injective.injOn
  derivativeEquiv _ := (properLorentzFourCLE L).symm
  derivative p _ := original_eh_inverse_affine_derivative b L p
  regular p _ := original_eh_inverse_affine_regular b L p
  symmetric := wick_native_flat_symmetric
  baseline p _ := original_eh_native_flat_lorentz p
  perturbed p _ := original_eh_act_metric_lorentz H inside p
  test := original_eh_constructed_affine_test b L H

theorem original_eh_original_frame_action (κ Λ : ℝ) (b : Spacetime)
    (L : ProperLorentzTransform) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    originalEHRelativeAction κ Λ wickNativeFlatMetric (wickNativeAffineMetricTest b L H) =
      originalEHRelativeAction κ Λ wickNativeFlatMetric H := by
  have action := (originalEHOriginalFrameTransport b L H inside).action_square κ Λ
  simpa only [originalEHOriginalFrameTransport, original_eh_affine_flat_pullback] using action

theorem original_eh_original_frame_evaluator (κ Λ : ℝ) (b : Spacetime)
    (L : ProperLorentzTransform) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    (originalEHFiniteUse κ Λ wickNativeFlatMetric (wickNativeAffineMetricTest b L H)).2 =
      (originalEHFiniteUse κ Λ wickNativeFlatMetric H).2 := by
  have evaluator := (originalEHOriginalFrameTransport b L H inside).finite_evaluator_square κ Λ
  simpa only [originalEHOriginalFrameTransport, original_eh_affine_flat_pullback] using evaluator

theorem original_eh_original_frame_domain (κ Λ : ℝ) (b : Spacetime)
    (L : ProperLorentzTransform) (H : MetricSourceProbe Ω)
    (inside : H ∈ wickOriginalMetricNeighborhood Ω) :
    OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric H ↔
      OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric (wickNativeAffineMetricTest b L H) := by
  have domain := (originalEHOriginalFrameTransport b L H inside).finite_use_domain_iff κ Λ
  simpa only [originalEHOriginalFrameTransport, original_eh_affine_flat_pullback] using domain

theorem original_eh_constructed_frame_metric (b : Spacetime) (L : ProperLorentzTransform)
    (H : MetricSourceProbe Ω) :
    originalEHActMetric (wickNativeAffineMetricTest b L H) =
      coordinateMetricPullback (originalEHActMetric H) (wickAffineCoordinateHomeomorph b L).symm := by
  unfold originalEHActMetric
  rw [← original_eh_pullback_perturbation wickNativeFlatMetric H _ _
    (original_eh_constructed_affine_test b L H),original_eh_affine_flat_pullback]

theorem original_eh_constructed_frame_lorentz (b : Spacetime) (L : ProperLorentzTransform)
    (H : MetricSourceProbe Ω) (inside : H ∈ wickOriginalMetricNeighborhood Ω)
    (p : CoordinatePoint) : C2LorentzMetricAt (originalEHActMetric (wickNativeAffineMetricTest b L H)) p := by
  rw [original_eh_constructed_frame_metric]
  exact original_eh_c2_lorentz_pullback _ _ p
    (original_eh_act_metric_lorentz H inside _)
    (original_eh_inverse_affine_regular b L p) _ (original_eh_inverse_affine_derivative b L p)

theorem original_eh_transported_original_domain (κ Λ : ℝ) (coupling : κ ≠ 0)
    (b : Spacetime) (L : ProperLorentzTransform)
    (J : MetricSourceProbe (wickAffineMetricRegion b L Ω))
    (inside : J ∈ wickTransportedMetricDomain b L Ω) :
    OriginalEHFiniteUseDomain κ Λ wickNativeFlatMetric J := by
  obtain ⟨H,hH,rfl⟩ := inside
  exact (original_eh_original_frame_domain κ Λ b L H hH).mp
    (original_eh_original_act_admitted κ Λ coupling H hH)

end
end AASCKleinGordon
