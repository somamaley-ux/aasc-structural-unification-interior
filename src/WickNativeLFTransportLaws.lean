import WickNativeLFTransport
import WickPoincareRayTransport

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickMetricProbeRegionCongr {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ) :
    MetricSourceProbe Ω ≃L[ℝ] MetricSourceProbe Ξ := h ▸ ContinuousLinearEquiv.refl ℝ _

theorem wick_metric_probe_region_congr_apply {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ)
    (H : MetricSourceProbe Ω) (x : CoordinatePoint) : wickMetricProbeRegionCongr h H x=H x := by
  subst Ξ
  rfl

theorem wick_affine_coordinate_comp (b c : Spacetime) (L M : ProperLorentzTransform)
    (x : CoordinatePoint) : wickAffineCoordinateHomeomorph b L (wickAffineCoordinateHomeomorph c M x)=
      wickAffineCoordinateHomeomorph (b+spacetimeLorentzCLE L c) (L*M) x := by
  change wickSpacetimeCoordinates b+L.val (wickSpacetimeCoordinates c+M.val x)=
    wickSpacetimeCoordinates (b+spacetimeLorentzCLE L c)+(L*M).val x
  rw [map_add]
  change wickSpacetimeCoordinates b+(L.val (wickSpacetimeCoordinates c)+L.val (M.val x))=
    (wickSpacetimeCoordinates b+L.val (wickSpacetimeCoordinates c))+L.val (M.val x)
  abel

theorem wick_affine_region_comp (b c : Spacetime) (L M : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) :
    wickAffineMetricRegion b L (wickAffineMetricRegion c M Ω)=
      wickAffineMetricRegion (b+spacetimeLorentzCLE L c) (L*M) Ω := by
  apply Opens.ext
  change wickAffineCoordinateHomeomorph b L '' (wickAffineCoordinateHomeomorph c M '' (Ω : Set CoordinatePoint))=_
  rw [Set.image_image]
  congr 1
  funext x
  exact wick_affine_coordinate_comp b c L M x

theorem wick_affine_coordinate_one : wickAffineCoordinateHomeomorph 0 1=Homeomorph.refl CoordinatePoint := by
  apply Homeomorph.ext
  intro x
  change wickSpacetimeCoordinates 0+(1 : ProperLorentzTransform).val x=x
  simp

theorem wick_affine_region_one (Ω : Opens CoordinatePoint) : wickAffineMetricRegion 0 1 Ω=Ω := by
  apply Opens.ext
  change wickAffineCoordinateHomeomorph 0 1 '' (Ω : Set CoordinatePoint)=_
  rw [wick_affine_coordinate_one]
  exact Set.image_id _

theorem wick_native_affine_test_one (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickMetricProbeRegionCongr (wick_affine_region_one Ω) (wickNativeAffineMetricTest 0 1 H)=H := by
  apply TestFunction.ext
  intro x
  rw [wick_metric_probe_region_congr_apply]
  change wickTensorCongruenceLM (wickLorentzMatrix (1 : ProperLorentzTransform)⁻¹)
    (H ((wickAffineCoordinateHomeomorph 0 1).symm x))=H x
  rw [inv_one,wick_lorentz_matrix_one,wick_tensor_congruence_one,wick_affine_coordinate_one]
  rfl

theorem wick_native_affine_test_comp (b c : Spacetime) (L M : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickMetricProbeRegionCongr (wick_affine_region_comp b c L M Ω)
      (wickNativeAffineMetricTest b L (wickNativeAffineMetricTest c M H))=
        wickNativeAffineMetricTest (b+spacetimeLorentzCLE L c) (L*M) H := by
  apply TestFunction.ext
  intro x
  rw [wick_metric_probe_region_congr_apply]
  change wickTensorCongruenceLM (wickLorentzMatrix L⁻¹)
      (wickTensorCongruenceLM (wickLorentzMatrix M⁻¹)
        (H ((wickAffineCoordinateHomeomorph c M).symm ((wickAffineCoordinateHomeomorph b L).symm x))))=
    wickTensorCongruenceLM (wickLorentzMatrix (L*M)⁻¹)
      (H ((wickAffineCoordinateHomeomorph (b+spacetimeLorentzCLE L c) (L*M)).symm x))
  rw [wick_tensor_congruence_comp,← wick_lorentz_matrix_mul,mul_inv_rev]
  congr 2
  apply (wickAffineCoordinateHomeomorph (b+spacetimeLorentzCLE L c) (L*M)).injective
  rw [← wick_affine_coordinate_comp]
  simp only [Homeomorph.apply_symm_apply]

def wickKGFirstActInverse (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct (wickAffineMetricRegion b L Ω)) :
    WickKGFirstMetricAct Ω where
  test := wickNativeAffineMetricInverseCLM b L Ω δ.test
  parameter := δ.parameter
  rate := δ.rate
  parameter_zero := δ.parameter_zero
  parameter_C1 := δ.parameter_C1
  derivative := δ.derivative

def wickKGFirstActPoincareEquiv (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : WickKGFirstMetricAct Ω ≃
      WickKGFirstMetricAct (wickAffineMetricRegion b L Ω) where
  toFun := wickKGFirstActPoincare b L
  invFun := wickKGFirstActInverse b L
  left_inv δ := by
    cases δ with
    | mk H parameter rate zero C1 derivative =>
      dsimp only [wickKGFirstActInverse,wickKGFirstActPoincare]
      congr 1
      exact wick_native_affine_inverse_left b L Ω H
  right_inv δ := by
    cases δ with
    | mk H parameter rate zero C1 derivative =>
      dsimp only [wickKGFirstActInverse,wickKGFirstActPoincare]
      congr 1
      exact wick_native_affine_inverse_right b L Ω H

def wickKGProtocolPoincareEquiv (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : WickKGOriginalProtocol Ω ≃
      WickKGOriginalProtocol (wickAffineMetricRegion b L Ω) where
  toFun := wickKGProtocolPoincare b L
  invFun
    | .finite H => .finite (wickNativeAffineMetricInverseCLM b L Ω H)
    | .first δ => .first (wickKGFirstActInverse b L δ)
  left_inv π := by
    cases π with
    | finite H => exact congrArg WickKGOriginalProtocol.finite (wick_native_affine_inverse_left b L Ω H)
    | first δ => exact congrArg WickKGOriginalProtocol.first ((wickKGFirstActPoincareEquiv b L Ω).left_inv δ)
  right_inv π := by
    cases π with
    | finite H => exact congrArg WickKGOriginalProtocol.finite (wick_native_affine_inverse_right b L Ω H)
    | first δ => exact congrArg WickKGOriginalProtocol.first ((wickKGFirstActPoincareEquiv b L Ω).right_inv δ)

theorem wick_KG_full_protocol_transport_bijective (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : Function.Bijective
      (wickKGProtocolPoincare b L : WickKGOriginalProtocol Ω →
        WickKGOriginalProtocol (wickAffineMetricRegion b L Ω)) :=
  (wickKGProtocolPoincareEquiv b L Ω).bijective

end AASCKleinGordon
