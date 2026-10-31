import WickNativeDeclaredSourcePresentation
import WickProtocolTransportLaws

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open AASCSemanticExhaustion
namespace AASCKleinGordon

theorem wick_native_affine_cle_apply (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (H : MetricSourceProbe Ω) :
    wickNativeAffineMetricTestCLE b L Ω H=wickNativeAffineMetricTest b L H :=
  congrFun (wick_native_affine_clm_eq b L Ω) H

theorem wick_native_affine_cle_inverse_apply (b : Spacetime) (L : ProperLorentzTransform)
    (Ω : Opens CoordinatePoint) (J : MetricSourceProbe (wickAffineMetricRegion b L Ω)) :
    (wickNativeAffineMetricTestCLE b L Ω).symm J=wickNativeAffineMetricInverseCLM b L Ω J := rfl

theorem wick_original_presentation_source_transport (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) :
    (wickTransportedNativeSourcePresentation a b L s u Ω).functional
      (wickNativeAffineMetricTestCLE b L Ω H)=
        (wickOriginalNativeSourcePresentation a s u Ω).functional H := by
  rw [(wickTransportedNativeSourcePresentation a b L s u Ω).same_original_source,
    (wickOriginalNativeSourcePresentation a s u Ω).same_original_source,wick_native_affine_cle_apply]
  exact wick_original_native_response_poincare a b L s u Ω H

theorem wick_original_presentation_full_readout_transport (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint)
    (π : WickKGOriginalProtocol Ω) :
    (wickTransportedNativeSourcePresentation a b L s u Ω).entire_readout
      (wickKGProtocolPoincareEquiv b L Ω π)=
        (wickOriginalNativeSourcePresentation a s u Ω).entire_readout π := by
  rw [wick_original_presentation_readout_provenance,wick_transported_presentation_readout_provenance]
  exact wick_KG_all_readouts_poincare a b L s u Ω π

theorem wick_original_presentation_MetResp_transport (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint)
    (H : MetricSourceProbe Ω) (z : ℝ) :
    (∃ π,wickKGOriginalMetInc (wickNativeAffineMetricTestCLE b L Ω H) π ∧
      (wickTransportedNativeSourcePresentation a b L s u Ω).entire_readout π=.first z) ↔
    (∃ π,wickKGOriginalMetInc H π ∧
      (wickOriginalNativeSourcePresentation a s u Ω).entire_readout π=.first z) := by
  rw [(wickTransportedNativeSourcePresentation a b L s u Ω).source_graph,
    (wickOriginalNativeSourcePresentation a s u Ω).source_graph,
    wick_original_presentation_source_transport]

theorem wick_original_presentation_represented_duality (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    (wickTransportedNativeSourcePresentation a b L s u Ω).represented=
      representedMetricSource
        ((wickOriginalNativeSourcePresentation a s u Ω).functional.comp
          (wickNativeAffineMetricTestCLE b L Ω).symm.toContinuousLinearMap) := by
  change representedMetricSource (wickKGFirstOperationalFunctional a s (corePoincare a b L u)
    (wickAffineMetricRegion b L Ω))=
      representedMetricSource ((wickKGFirstOperationalFunctional a s u Ω).comp _)
  rw [wick_KG_first_operational_functional_same,wick_KG_first_operational_functional_same]
  exact wick_native_represented_source_pushforward a b L s u Ω

theorem wick_original_presentation_ward_transport (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint)
    (X : CoordinateVectorProbe Ω) :
    (wickTransportedNativeSourcePresentation a b L s u Ω).functional
      (wickNativeAffineMetricTestCLE b L Ω
        (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X))=0 := by
  rw [wick_original_presentation_source_transport,
    (wickOriginalNativeSourcePresentation a s u Ω).same_original_source]
  exact original_wick_native_real_lie_ward a s u Ω X

theorem wick_original_support_envelope_affine (b : Spacetime) (L : ProperLorentzTransform) :
    wickAffineCoordinateHomeomorph b L '' wickOriginalClosedSupportEnvelope=
      wickOriginalClosedSupportEnvelope :=
  Set.image_univ_of_surjective (wickAffineCoordinateHomeomorph b L).surjective

/-- The lawful transport contains test/protocol equivalences, the entire
readout ledger and MetResp, the dual density, and proved source ledgers.
It is stronger than identifying witnesses alone. -/
structure WickNativeDeclaredSourceTransport (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) where
  tests : MetricSourceProbe Ω ≃L[ℝ] MetricSourceProbe (wickAffineMetricRegion b L Ω)
  tests_actual : tests=wickNativeAffineMetricTestCLE b L Ω
  protocols : WickKGOriginalProtocol Ω ≃ WickKGOriginalProtocol (wickAffineMetricRegion b L Ω)
  protocols_actual : protocols=wickKGProtocolPoincareEquiv b L Ω
  incident : ∀ H π,wickKGOriginalMetInc (tests H) (protocols π) ↔ wickKGOriginalMetInc H π
  source : ∀ H,(wickTransportedNativeSourcePresentation a b L s u Ω).functional (tests H)=
    (wickOriginalNativeSourcePresentation a s u Ω).functional H
  full_readout : ∀ π,(wickTransportedNativeSourcePresentation a b L s u Ω).entire_readout (protocols π)=
    (wickOriginalNativeSourcePresentation a s u Ω).entire_readout π
  tensor_duality : (wickTransportedNativeSourcePresentation a b L s u Ω).represented=
    representedMetricSource ((wickOriginalNativeSourcePresentation a s u Ω).functional.comp
      tests.symm.toContinuousLinearMap)
  ward_mapped : ∀ X,(wickTransportedNativeSourcePresentation a b L s u Ω).functional
    (tests (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X))=0
  support_envelope : wickAffineCoordinateHomeomorph b L '' wickOriginalClosedSupportEnvelope=
    wickOriginalClosedSupportEnvelope
  original_ledgers : WickNativeOriginalTensorLedger a s u
  transported_ledgers : WickNativeOriginalTensorLedger a s (corePoincare a b L u)

def wickNativeDeclaredSourceTransport (a : Parameters) (b : Spacetime)
    (L : ProperLorentzTransform) (s : ℝ) (u : FiniteParticleCore) (Ω : Opens CoordinatePoint) :
    WickNativeDeclaredSourceTransport a b L s u Ω where
  tests := wickNativeAffineMetricTestCLE b L Ω
  tests_actual := rfl
  protocols := wickKGProtocolPoincareEquiv b L Ω
  protocols_actual := rfl
  incident H π := by rw [wick_native_affine_cle_apply]; exact wick_KG_incidence_poincare b L Ω H π
  source := wick_original_presentation_source_transport a b L s u Ω
  full_readout := wick_original_presentation_full_readout_transport a b L s u Ω
  tensor_duality := wick_original_presentation_represented_duality a b L s u Ω
  ward_mapped := wick_original_presentation_ward_transport a b L s u Ω
  support_envelope := wick_original_support_envelope_affine b L
  original_ledgers := wickNativeOriginalTensorLedger a s u
  transported_ledgers := wickNativeOriginalTensorLedger a s (corePoincare a b L u)

end AASCKleinGordon
