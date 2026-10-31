import WickPoincareFiniteAction
import WickNativeAffineMetricLaws

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace Filter
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickKGFirstActPoincare (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    WickKGFirstMetricAct (wickAffineMetricRegion b L Ω) where
  test := wickNativeAffineMetricTest b L δ.test
  parameter := δ.parameter
  rate := δ.rate
  parameter_zero := δ.parameter_zero
  parameter_C1 := δ.parameter_C1
  derivative := δ.derivative

def wickKGProtocolPoincare (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} : WickKGOriginalProtocol Ω →
      WickKGOriginalProtocol (wickAffineMetricRegion b L Ω)
  | .finite H => .finite (wickNativeAffineMetricTest b L H)
  | .first δ => .first (wickKGFirstActPoincare b L δ)

theorem wick_KG_poincare_tangent (b : Spacetime) (L : ProperLorentzTransform)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstTangent (wickKGFirstActPoincare b L δ)=
      wickNativeAffineMetricTest b L (wickKGFirstTangent δ) :=
  (wick_native_affine_test_smul b L δ.rate δ.test).symm

theorem wick_original_native_response_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    originalWickNativeRealMetricResponse a s (corePoincare a b L u)
      (wickAffineMetricRegion b L Ω) (wickNativeAffineMetricTest b L H)=
      originalWickNativeRealMetricResponse a s u Ω H := by
  have same : (fun t : ℝ => wickOriginalRealFiniteAction a s (corePoincare a b L u)
      (t • wickNativeAffineMetricTest b L H)) =
      (fun t : ℝ => wickOriginalRealFiniteAction a s u (t • H)) := by
    funext t
    rw [← wick_native_affine_test_smul]
    exact wick_original_real_finite_action_poincare a b L s u (t • H)
  have transformed := wick_original_real_finite_action_gateaux_derivative a s
    (corePoincare a b L u) (wickAffineMetricRegion b L Ω) (wickNativeAffineMetricTest b L H)
  rw [same] at transformed
  exact transformed.unique (wick_original_real_finite_action_gateaux_derivative a s u Ω H)

theorem wick_KG_first_output_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore)
    {Ω : Opens CoordinatePoint} (δ : WickKGFirstMetricAct Ω) :
    wickKGFirstOutput a s (corePoincare a b L u) (wickKGFirstActPoincare b L δ)=
      wickKGFirstOutput a s u δ := by
  rw [wick_KG_original_first_output_computed, wick_KG_poincare_tangent,
    wick_original_native_response_poincare, wick_KG_original_first_output_computed]

/-- A transported finite chart uses the SAME action. The coordinate box is
transported with its requests; no boost invariance of that box is asserted. -/
def wickKGTransportedChartOutput (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (b : Spacetime) (L : ProperLorentzTransform) (Ω : Opens CoordinatePoint) :
    WickKGOriginalProtocol (wickAffineMetricRegion b L Ω) → WickKGOriginalReadout := by
  classical
  exact fun
    | .finite J => if J∈wickTransportedMetricDomain b L Ω then
        .finite (wickOriginalRealFiniteAction a s u J) else .failed
    | .first δ => .first (wickKGFirstOutput a s u δ)

theorem wick_KG_all_readouts_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (π : WickKGOriginalProtocol Ω) :
    wickKGTransportedChartOutput a s (corePoincare a b L u) b L Ω
      (wickKGProtocolPoincare b L π)=wickKGOriginalOutput a s u π := by
  classical
  cases π with
  | finite H =>
    by_cases inside : H∈wickOriginalMetricNeighborhood Ω
    · have transported := (wick_transported_metric_domain_exact b L Ω H).mpr inside
      simp only [wickKGProtocolPoincare, wickKGTransportedChartOutput, if_pos transported,
        wickKGOriginalOutput, dif_pos inside, wickKGFiniteActionCarrier]
      exact congrArg WickKGOriginalReadout.finite
        (wick_original_real_finite_action_poincare a b L s u H)
    · have outside : wickNativeAffineMetricTest b L H∉wickTransportedMetricDomain b L Ω :=
        fun h => inside ((wick_transported_metric_domain_exact b L Ω H).mp h)
      simp only [wickKGProtocolPoincare, wickKGTransportedChartOutput, if_neg outside,
        wickKGOriginalOutput, dif_neg inside]
  | first δ =>
    exact congrArg WickKGOriginalReadout.first (wick_KG_first_output_poincare a b L s u δ)

theorem wick_KG_response_graph_poincare (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) (z : ℝ) :
    wickKGOriginalMetResp a s (corePoincare a b L u)
      (wickNativeAffineMetricTest b L H) z ↔ wickKGOriginalMetResp a s u H z := by
  rw [wick_KG_original_response_graph, wick_KG_original_response_graph,
    wick_original_native_response_poincare]

end AASCKleinGordon
