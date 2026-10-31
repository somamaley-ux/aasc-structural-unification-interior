import WickDeclaredSourceFunctional
import WickPoincareIncidence
import WickNativeLFTransportLaws
import WickNativeSourceTensorLedger

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

/-- Native LF source presentation for the FIXED declared finite/first grammar.
The sum-valued readout and exact failures are retained. This is not an identity
with an arbitrary earlier, richer ledger. -/
structure WickNativeDeclaredSourcePresentation (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) where
  domain_open : IsOpen D
  domain_zero : (0 : MetricSourceProbe Ω)∈D
  metric_admissible : ∀ H∈D,∀ x,WickIntrinsicLorentzSignature (wickOriginalFiniteMetric H x) ∧
    (wickOriginalFiniteMetric H x).det≠0
  functional : MetricSourceProbe Ω →L[ℝ] ℝ
  constructed_from_first_acts : functional=wickKGFirstOperationalFunctional a s u Ω
  same_original_source : functional=originalWickNativeRealMetricResponse a s u Ω
  entire_readout : WickKGOriginalProtocol Ω → WickKGOriginalReadout
  actual_readout : entire_readout=wickKGChartOutput a s u D
  full_grammar : ∀ π : WickKGOriginalProtocol Ω,(∃ H,π=.finite H) ∨ (∃ δ,π=.first δ)
  exact_failures : ∀ π,entire_readout π=.failed ↔ ∃ H,π=.finite H ∧ H∉D
  all_tests_incident : ∀ H : MetricSourceProbe Ω,∃ π : WickKGOriginalProtocol Ω,wickKGOriginalMetInc H π
  source_graph : ∀ H z,(∃ π,wickKGOriginalMetInc H π ∧ entire_readout π=.first z) ↔ functional H=z
  tensor_ledger : WickNativeOriginalTensorLedger a s u
  represented : SymmetricSourceComponents Ω
  half_pairing : ∀ H,(1/2 : ℝ)*metricSourcePairing represented H=functional H
  representation_unique : ∀ T : SymmetricSourceComponents Ω,
    (∀ H,(1/2 : ℝ)*metricSourcePairing T H=functional H) → T=represented

def wickNativeDeclaredSourcePresentation (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) (D : Set (MetricSourceProbe Ω)) (hD : IsOpen D)
    (h0 : (0 : MetricSourceProbe Ω)∈D)
    (metric : ∀ H∈D,∀ x,WickIntrinsicLorentzSignature (wickOriginalFiniteMetric H x) ∧
      (wickOriginalFiniteMetric H x).det≠0) : WickNativeDeclaredSourcePresentation a s u Ω D where
  domain_open := hD
  domain_zero := h0
  metric_admissible := metric
  functional := wickKGFirstOperationalFunctional a s u Ω
  constructed_from_first_acts := rfl
  same_original_source := wick_KG_first_operational_functional_same a s u Ω
  entire_readout := wickKGChartOutput a s u D
  actual_readout := rfl
  full_grammar := wick_KG_declared_protocol_constructor_complete Ω
  exact_failures := wick_KG_chart_failure_exact a s u Ω D
  all_tests_incident H := ⟨.first (wickKGIdentityAct H),
    ⟨wickKGIdentityAct H,rfl,wick_KG_identity_tangent H⟩⟩
  source_graph H z := by
    rw [wick_KG_first_operational_functional_same]
    exact wick_KG_chart_response_graph a s u Ω D H z
  tensor_ledger := wickNativeOriginalTensorLedger a s u
  represented := representedMetricSource (wickKGFirstOperationalFunctional a s u Ω)
  half_pairing := constructed_metric_source_represents _
  representation_unique := constructed_metric_source_unique _

def wickOriginalNativeSourcePresentation (a : Parameters) (s : ℝ) (u : FiniteParticleCore)
    (Ω : Opens CoordinatePoint) :
    WickNativeDeclaredSourcePresentation a s u Ω (wickOriginalMetricNeighborhood Ω) :=
  wickNativeDeclaredSourcePresentation a s u Ω (wickOriginalMetricNeighborhood Ω)
    (wick_original_metric_neighborhood_open Ω) (wick_original_metric_neighborhood_zero Ω)
      (fun H hH x => ⟨wick_original_signature_is_intrinsic _
        (wick_original_metric_domain_fixed_signature Ω H hH x),
          wick_original_metric_domain_nondegenerate Ω H hH x⟩)

theorem wick_transported_native_domain_zero (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) : (0 : MetricSourceProbe (wickAffineMetricRegion b L Ω))∈
      wickTransportedMetricDomain b L Ω := by
  refine ⟨0,wick_original_metric_neighborhood_zero Ω,?_⟩
  rw [← wick_native_affine_clm_eq]
  exact map_zero _

def wickTransportedNativeSourcePresentation (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    WickNativeDeclaredSourcePresentation a s (corePoincare a b L u)
      (wickAffineMetricRegion b L Ω) (wickTransportedMetricDomain b L Ω) :=
  wickNativeDeclaredSourcePresentation a s (corePoincare a b L u) (wickAffineMetricRegion b L Ω)
    (wickTransportedMetricDomain b L Ω) (wick_transported_metric_domain_open b L Ω)
      (wick_transported_native_domain_zero b L Ω) (wick_transported_metric_signature b L Ω)

theorem wick_original_presentation_readout_provenance (a : Parameters) (s : ℝ)
    (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    (wickOriginalNativeSourcePresentation a s u Ω).entire_readout=wickKGOriginalOutput a s u :=
  wick_KG_chart_base_is_original a s u Ω

theorem wick_transported_presentation_readout_provenance (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    (wickTransportedNativeSourcePresentation a b L s u Ω).entire_readout=
      wickKGTransportedChartOutput a s (corePoincare a b L u) b L Ω :=
  wick_KG_chart_transport_is_original a s (corePoincare a b L u) b L Ω

theorem wick_native_source_response_pushforward (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    originalWickNativeRealMetricResponse a s (corePoincare a b L u) (wickAffineMetricRegion b L Ω)=
      (originalWickNativeRealMetricResponse a s u Ω).comp (wickNativeAffineMetricInverseCLM b L Ω) := by
  ext J
  have transport := wick_original_native_response_poincare a b L s u Ω
    (wickNativeAffineMetricInverseCLM b L Ω J)
  rw [wick_native_affine_inverse_right] at transport
  exact transport

/-- Tensor-density pushforward is defined by duality and follows from the
actual all-test identity. The off-diagonal weights and half-pairing persist. -/
theorem wick_native_represented_source_pushforward (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    representedMetricSource
      (originalWickNativeRealMetricResponse a s (corePoincare a b L u) (wickAffineMetricRegion b L Ω))=
    representedMetricSource ((originalWickNativeRealMetricResponse a s u Ω).comp
      (wickNativeAffineMetricInverseCLM b L Ω)) :=
  congrArg representedMetricSource (wick_native_source_response_pushforward a b L s u Ω)

end AASCKleinGordon
