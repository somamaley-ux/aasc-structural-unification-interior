import WickNativeDeclaredSourceTransport
import WickNativePresentationGerms

noncomputable section
set_option maxHeartbeats 1500000
open TopologicalSpace
open scoped Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickRayPresentationState (a : Parameters) (ray : Quotient wickCoreRaySetoid) : FiniteParticleCore :=
  originalWickUnitRepresentative a ray.out.val

def wickNativeRaySourcePresentation (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)
    (ray : Quotient wickCoreRaySetoid) :
    WickNativeDeclaredSourcePresentation a s (wickRayPresentationState a ray) Ω
      (wickOriginalMetricNeighborhood Ω) :=
  wickOriginalNativeSourcePresentation a s (wickRayPresentationState a ray) Ω

theorem wick_native_ray_presentation_same_source (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) :
    (wickNativeRaySourcePresentation a s Ω ray).functional H=originalWickRayMetricResponse a s Ω ray H := by
  have functional := (wickNativeRaySourcePresentation a s Ω ray).same_original_source
  simp only [wickRayPresentationState] at functional
  have same := original_wick_ray_source_is_actual_unit_response a s Ω ray.out
  rw [Quotient.out_eq] at same
  exact DFunLike.congr_fun (functional.trans same.symm) H

theorem wick_native_ray_presentation_same_readout (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (π : WickKGOriginalProtocol Ω) :
    (wickNativeRaySourcePresentation a s Ω ray).entire_readout π=wickKGOriginalRayOutput a s Ω ray π := by
  change (wickOriginalNativeSourcePresentation a s (wickRayPresentationState a ray) Ω).entire_readout π=_
  rw [wick_original_presentation_readout_provenance]
  have same : wickKGOriginalRayOutput a s Ω (Quotient.mk wickCoreRaySetoid ray.out) π=
      wickKGOriginalOutput a s (originalWickUnitRepresentative a ray.out.val) π := rfl
  rw [Quotient.out_eq] at same
  exact same.symm

theorem wick_native_ray_presentation_response_graph (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (ray : Quotient wickCoreRaySetoid) (H : MetricSourceProbe Ω) (z : ℝ) :
    (∃ π,wickKGOriginalMetInc H π ∧
      (wickNativeRaySourcePresentation a s Ω ray).entire_readout π=.first z) ↔
        originalWickRayMetricResponse a s Ω ray H=z := by
  rw [(wickNativeRaySourcePresentation a s Ω ray).source_graph,wick_native_ray_presentation_same_source]

/-- Native declared-grammar normalized source package. This combines actual
prequotient invariance, original ray outputs, lawful geometric transport and
the previously proved graph/strong/joint/norm-squared analytic attachments. -/
structure WickNativeNormalizedSourceAssembly (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) where
  presentations : ∀ ray,WickNativeDeclaredSourcePresentation a s (wickRayPresentationState a ray) Ω
    (wickOriginalMetricNeighborhood Ω)
  same_source : ∀ ray H,(presentations ray).functional H=originalWickRayMetricResponse a s Ω ray H
  same_readout : ∀ ray π,(presentations ray).entire_readout π=wickKGOriginalRayOutput a s Ω ray π
  germs_admitted : ∀ (ray : Quotient wickCoreRaySetoid) (δ : WickKGFirstMetricAct Ω),∀ᶠ t in nhds 0,
    δ.parameter t • δ.test∈wickOriginalMetricNeighborhood Ω
  prequotient_invariant : ∀ (u v : WickNonzeroCore),wickCoreRaySetoid.r u v →
    ∀ π : WickKGOriginalProtocol Ω,
      wickKGOriginalOutput a s (originalWickUnitRepresentative a u.val) π=
        wickKGOriginalOutput a s (originalWickUnitRepresentative a v.val) π
  geometric_source : ∀ b L ray H,
    originalWickRayMetricResponse a s (wickAffineMetricRegion b L Ω)
      (wickPoincareRayAction a b L ray) (wickNativeAffineMetricTest b L H)=
        originalWickRayMetricResponse a s Ω ray H
  geometric_entire_family : ∀ b L ray π,
    wickKGTransportedRayOutput a s b L Ω (wickPoincareRayAction a b L ray)
      (wickKGProtocolPoincare b L π)=wickKGOriginalRayOutput a s Ω ray π
  native_geometric_transport : ∀ b L ray,
    WickNativeDeclaredSourceTransport a b L s (wickRayPresentationState a ray) Ω
  joint_ray_evaluation : Continuous (fun z : WickNonzeroCore × MetricSourceProbe Ω =>
    originalWickRayMetricResponse a s Ω (Quotient.mk wickCoreRaySetoid z.1) z.2)
  graph_topology : wickDeclaredGraphTopology a=(inferInstance : TopologicalSpace FiniteParticleCore)
  strong_continuity : Continuous (originalWickNativeStrongResponse a s Ω)
  strong_action_derivative : ∀ H v u,
    HasDerivAt (originalWickScalarRelativeAction a s u v (wickNativeMetricVariation H))
      (originalWickNativeStrongResponse a s Ω H v u) 0
  full_strong_same_tensor : ∀ H v u,originalWickNativeFullStressOperator a s Ω H v u=
    originalWickStressMetricDistribution a s u v (nativeToWickMetricTest Ω H)
  norm_squared_extension : ∀ u : FiniteParticleCore,u≠0 →
    originalWickCoreNormSq a u • originalWickNormalizedRayResponse a s u Ω=
      originalWickNativeRealMetricResponse a s u Ω

def wickNativeNormalizedSourceAssembly (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint) :
    WickNativeNormalizedSourceAssembly a s Ω where
  presentations := wickNativeRaySourcePresentation a s Ω
  same_source := wick_native_ray_presentation_same_source a s Ω
  same_readout := wick_native_ray_presentation_same_readout a s Ω
  germs_admitted := fun ray δ => wick_declared_presentation_every_first_germ_admitted a s
    (wickRayPresentationState a ray) Ω _ (wickNativeRaySourcePresentation a s Ω ray) δ
  prequotient_invariant := fun u v huv π => wick_KG_original_normalized_prequotient_readouts a s u v huv π
  geometric_source := fun b L ray H => wick_original_ray_source_poincare a b L s Ω ray H
  geometric_entire_family := fun b L ray π => wick_KG_entire_ray_family_poincare a b L s Ω ray π
  native_geometric_transport := fun b L ray =>
    wickNativeDeclaredSourceTransport a b L s (wickRayPresentationState a ray) Ω
  joint_ray_evaluation := original_wick_unit_ray_evaluation_joint_core_continuous a s Ω
  graph_topology := wick_declared_graph_topology_eq_original a
  strong_continuity := (originalWickNativeStrongResponse a s Ω).continuous
  strong_action_derivative := original_wick_native_strong_response_actual_action_derivative a s Ω
  full_strong_same_tensor := original_wick_native_full_stress_operator_same_tensor a s Ω
  norm_squared_extension := fun u hu => original_wick_norm_squared_vector_extension a s u hu Ω

end AASCKleinGordon
