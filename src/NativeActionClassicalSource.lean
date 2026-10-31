import NativeActionSourceAssembly
import RegularSourceTestSeparation

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Filter TopologicalSpace MeasureTheory
open scoped Topology BigOperators

variable {Ω : Opens CoordinatePoint} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Receiving data for the original action-presentable source subclass.
The analytic and native symmetry receipts are explicit. No tensor, Ward
profile, source conservation or gravitational equation occurs in these fields.
The action is the matter action, with the metric varied separately. -/
structure NativeActionSourceData (Ω : Opens CoordinatePoint) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  action : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ
  finiteRegular : NativeActionFiniteParamDifferentiable action
  hadamard : NativeActionHadamardAtZero action
  metricLF : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
    Continuous (nativeActionDirectional (nativeMetricRestrictedAction action) ∘ TestFunction.ofSupportedIn hK)
  metric : MetricField
  metricSmooth : SmoothCoordinateMetric metric
  metricSymmetric : MetricFieldSymmetric metric
  matterLie : CoordinateVectorProbe Ω →L[ℝ] NativeMatterProbe Ω F
  symmetryCurve : CoordinateVectorProbe Ω → NativeActionCurve (MetricSourceProbe Ω × NativeMatterProbe Ω F)
  native_tangent : ∀ X, (symmetryCurve X).tangent =
    (compactMetricLieCLM Ω metric metricSmooth X,matterLie X)
  covariant : ∀ X, (fun t => action ((symmetryCurve X).curve t)) =ᶠ[𝓝 0] fun _ => action 0

def NativeActionSourceData.metricFunctional (d : NativeActionSourceData Ω F) :
    MetricSourceProbe Ω →L[ℝ] ℝ :=
  nativeTestActionFunctional (nativeMetricRestrictedAction d.action)
    (native_metric_restricted_action_finite_regular d.action d.finiteRegular) d.metricLF

def NativeActionSourceData.sourceDistribution (d : NativeActionSourceData Ω F) :
    SymmetricSourceComponents Ω := representedMetricSource d.metricFunctional

theorem native_action_source_data_protocol_attachment (d : NativeActionSourceData Ω F) :
    ∀ π : NativeActionCurve (MetricSourceProbe Ω),
      (1/2:ℝ)*metricSourcePairing d.sourceDistribution π.tangent=
        deriv (fun t => d.action (π.curve t,0)) 0 := by
  intro π
  rw [NativeActionSourceData.sourceDistribution,constructed_metric_source_represents]
  exact native_action_metric_functional_matches_every_original_protocol _
    (native_metric_restricted_action_finite_regular d.action d.finiteRegular)
    (native_metric_restricted_action_hadamard d.action d.hadamard) d.metricLF π

theorem native_action_source_data_internal_closure (d : NativeActionSourceData Ω F)
    (internal_equations : ∀ k, nativeActionDirectional (nativeMatterRestrictedAction d.action) k=0) :
    constructedSourceDivergence Ω d.metric d.metricSmooth d.sourceDistribution=0 :=
  native_action_internal_equations_imply_closed_source d.action d.finiteRegular d.hadamard d.metricLF
    d.metric d.metricSmooth d.metricSymmetric d.matterLie d.symmetryCurve d.native_tangent d.covariant
    internal_equations

theorem raised_source_tensor_density_symmetric (g T : MetricField) (symmetric : MetricFieldSymmetric T) :
    MetricFieldSymmetric (raisedSourceTensorDensity g T) := by
  intro p a b
  unfold raisedSourceTensorDensity
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [symmetric p j i]
  ring

def sourceDensityCoordinates (t : MetricField) (i : Fin 10) (p : CoordinatePoint) : ℝ :=
  t p (sourceSymmetricPair i).1 (sourceSymmetricPair i).2

theorem source_density_coordinates_recover (t : MetricField) (symmetric : MetricFieldSymmetric t) :
    (fun p a b => sourceDensityCoordinates t (sourceSymmetricIndex a b) p)=t := by
  funext p a b
  fin_cases a <;> fin_cases b <;> first | rfl | exact symmetric p _ _

/-- Native action closure -> equality of distributions -> compact-test
separation -> actual density current -> actual normal-coordinate covariant
divergence. Regularity is the manuscript's explicit smooth-source certificate;
the regular tensor must represent the already constructed action distribution
on every compact test, not merely fit selected histories. -/
theorem native_action_source_classical_covariant_conservation
    (d : NativeActionSourceData Ω F) (origin : (0:CoordinatePoint)∈Ω)
    (germ : C2NormalizedMetricGerm d.metric)
    (internal_equations : ∀ k, nativeActionDirectional (nativeMatterRestrictedAction d.action) k=0)
    (T : MetricField) (symmetric : MetricFieldSymmetric T)
    (regular : ∀ a b, DifferentiableAt ℝ (fun p => T p a b) 0)
    (densityRegular : ∀ i, ContDiff ℝ 1 (sourceDensityCoordinates (raisedSourceTensorDensity d.metric T) i))
    (represents : ∀ i φ, d.sourceDistribution i φ =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity d.metric T) i p * φ p) :
    coordinateDivergence d.metric T 0=0 := by
  have closed := native_action_source_data_internal_closure d internal_equations
  have current := regular_distributional_closure_implies_pointwise_density_current Ω d.metric
    d.metricSmooth d.sourceDistribution _ densityRegular represents closed
  have recovery := source_density_coordinates_recover (raisedSourceTensorDensity d.metric T)
    (raised_source_tensor_density_symmetric d.metric T symmetric)
  rw [recovery] at current
  funext e
  rw [← c2_normal_density_current_eq_covariant_divergence d.metric T germ regular e]
  exact current 0 origin e

#print axioms native_action_source_data_protocol_attachment
#print axioms native_action_source_data_internal_closure
#print axioms raised_source_tensor_density_symmetric
#print axioms source_density_coordinates_recover
#print axioms native_action_source_classical_covariant_conservation
end
end AASCSemanticExhaustion
