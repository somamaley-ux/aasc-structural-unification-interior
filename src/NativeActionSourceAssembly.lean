import NativeGeneralActionNoether
import NativeActionMetricTangent

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open Filter TopologicalSpace
open scoped Topology

variable {Ω : Opens CoordinatePoint}

theorem native_action_metric_functional_matches_every_original_protocol
    (S : MetricSourceProbe Ω → ℝ) (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (lf : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional S ∘ TestFunction.ofSupportedIn hK))
    (π : NativeActionCurve (MetricSourceProbe Ω)) :
    nativeTestActionFunctional S regular lf π.tangent = deriv (fun t => S (π.curve t)) 0 :=
  (native_action_curve_output_receipt S hadamard π).symm

theorem native_action_metric_functional_graph_is_original_response
    (S : MetricSourceProbe Ω → ℝ) (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (lf : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional S ∘ TestFunction.ofSupportedIn hK))
    (h : MetricSourceProbe Ω) (a : ℝ) :
    nativeTestActionFunctional S regular lf h=a ↔
      ∃ π : NativeActionCurve (MetricSourceProbe Ω), π.tangent=h ∧
        deriv (fun t => S (π.curve t)) 0=a := by
  constructor
  · intro ha
    refine ⟨nativeStraightActionCurve h,rfl,?_⟩
    rw [native_action_curve_output_receipt S hadamard]
    exact ha
  · rintro ⟨π,hπ,hout⟩
    change nativeActionDirectional S h=a
    rw [← hπ,← native_action_curve_output_receipt S hadamard π]
    exact hout

theorem native_action_operational_and_constructed_functionals_agree
    (S : MetricSourceProbe Ω → ℝ) (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (lf : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional S ∘ TestFunction.ofSupportedIn hK)) :
    ∃ lfOriginal,
      operationalMetricFunctional (nativeActionOperationalIncidence S regular hadamard) lfOriginal =
        nativeTestActionFunctional S regular lf := by
  have hcont : ∀ (K : Compacts CoordinatePoint) (hK : (K:Set CoordinatePoint)⊆Ω),
      Continuous (operationalMetricResponse (nativeActionOperationalIncidence S regular hadamard) ∘
        TestFunction.ofSupportedIn hK) := by
    intro K hK
    simpa only [Function.comp_def,native_action_operational_response_is_directional] using lf K hK
  refine ⟨hcont,?_⟩
  ext h
  exact native_action_operational_response_is_directional S regular hadamard h

theorem native_action_source_exists_unique_from_original_protocols
    (S : MetricSourceProbe Ω → ℝ) (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (lf : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional S ∘ TestFunction.ofSupportedIn hK)) :
    ∃! T : SymmetricSourceComponents Ω,
      ∀ π : NativeActionCurve (MetricSourceProbe Ω),
        (1/2:ℝ)*metricSourcePairing T π.tangent=deriv (fun t => S (π.curve t)) 0 := by
  let W := nativeTestActionFunctional S regular lf
  refine ⟨representedMetricSource W,?_,?_⟩
  · intro π
    rw [constructed_metric_source_represents]
    exact native_action_metric_functional_matches_every_original_protocol S regular hadamard lf π
  · intro T hT
    apply constructed_metric_source_unique W T
    intro h
    exact (hT (nativeStraightActionCurve h)).trans
      (native_action_curve_output_receipt S hadamard _)

#print axioms native_action_metric_functional_matches_every_original_protocol
#print axioms native_action_metric_functional_graph_is_original_response
#print axioms native_action_operational_and_constructed_functionals_agree
#print axioms native_action_source_exists_unique_from_original_protocols
end
end AASCSemanticExhaustion
