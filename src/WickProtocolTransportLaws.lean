import WickNativeLFTransportLaws

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickKGFirstActRegionCongr {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ) :
    WickKGFirstMetricAct Ω ≃ WickKGFirstMetricAct Ξ := h ▸ Equiv.refl _

def wickKGProtocolRegionCongr {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ) :
    WickKGOriginalProtocol Ω ≃ WickKGOriginalProtocol Ξ := h ▸ Equiv.refl _

theorem wick_first_act_ext {Ω : Opens CoordinatePoint} {δ ε : WickKGFirstMetricAct Ω}
    (test : δ.test=ε.test) (parameter : δ.parameter=ε.parameter) (rate : δ.rate=ε.rate) : δ=ε := by
  cases δ
  cases ε
  cases test
  cases parameter
  cases rate
  rfl

theorem wick_first_act_region_congr_fields {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ)
    (δ : WickKGFirstMetricAct Ω) :
    (wickKGFirstActRegionCongr h δ).test=wickMetricProbeRegionCongr h δ.test ∧
      (wickKGFirstActRegionCongr h δ).parameter=δ.parameter ∧
        (wickKGFirstActRegionCongr h δ).rate=δ.rate := by
  subst Ξ
  exact ⟨rfl,rfl,rfl⟩

theorem wick_protocol_region_congr_finite {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ)
    (H : MetricSourceProbe Ω) :
    wickKGProtocolRegionCongr h (.finite H)=.finite (wickMetricProbeRegionCongr h H) := by
  subst Ξ
  rfl

theorem wick_protocol_region_congr_first {Ω Ξ : Opens CoordinatePoint} (h : Ω=Ξ)
    (δ : WickKGFirstMetricAct Ω) :
    wickKGProtocolRegionCongr h (.first δ)=.first (wickKGFirstActRegionCongr h δ) := by
  subst Ξ
  rfl

theorem wick_first_act_poincare_one (Ω : Opens CoordinatePoint) (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstActRegionCongr (wick_affine_region_one Ω) (wickKGFirstActPoincare 0 1 δ)=δ := by
  apply wick_first_act_ext
  · rw [(wick_first_act_region_congr_fields _ _).1]
    exact wick_native_affine_test_one Ω δ.test
  · exact (wick_first_act_region_congr_fields _ _).2.1
  · exact (wick_first_act_region_congr_fields _ _).2.2

theorem wick_first_act_poincare_comp (b c : Spacetime) (L M : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstActRegionCongr (wick_affine_region_comp b c L M Ω)
      (wickKGFirstActPoincare b L (wickKGFirstActPoincare c M δ))=
        wickKGFirstActPoincare (b+spacetimeLorentzCLE L c) (L*M) δ := by
  apply wick_first_act_ext
  · rw [(wick_first_act_region_congr_fields _ _).1]
    exact wick_native_affine_test_comp b c L M Ω δ.test
  · exact (wick_first_act_region_congr_fields _ _).2.1
  · exact (wick_first_act_region_congr_fields _ _).2.2

theorem wick_protocol_poincare_one (Ω : Opens CoordinatePoint) (π : WickKGOriginalProtocol Ω) :
    wickKGProtocolRegionCongr (wick_affine_region_one Ω) (wickKGProtocolPoincare 0 1 π)=π := by
  cases π with
  | finite H =>
    rw [show wickKGProtocolPoincare 0 1 (.finite H)=.finite (wickNativeAffineMetricTest 0 1 H) from rfl,
      wick_protocol_region_congr_finite,wick_native_affine_test_one]
  | first δ =>
    rw [show wickKGProtocolPoincare 0 1 (.first δ)=.first (wickKGFirstActPoincare 0 1 δ) from rfl,
      wick_protocol_region_congr_first,wick_first_act_poincare_one]

theorem wick_protocol_poincare_comp (b c : Spacetime) (L M : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (π : WickKGOriginalProtocol Ω) :
    wickKGProtocolRegionCongr (wick_affine_region_comp b c L M Ω)
      (wickKGProtocolPoincare b L (wickKGProtocolPoincare c M π))=
        wickKGProtocolPoincare (b+spacetimeLorentzCLE L c) (L*M) π := by
  cases π with
  | finite H =>
    change wickKGProtocolRegionCongr _ (.finite (wickNativeAffineMetricTest b L
      (wickNativeAffineMetricTest c M H)))=.finite _
    rw [wick_protocol_region_congr_finite,wick_native_affine_test_comp]
  | first δ =>
    change wickKGProtocolRegionCongr _ (.first (wickKGFirstActPoincare b L
      (wickKGFirstActPoincare c M δ)))=.first _
    rw [wick_protocol_region_congr_first,wick_first_act_poincare_comp]

end AASCKleinGordon
