import NativeActionCurveProtocol
import OperationalSourceWardAssembly

/-! General action-presentable source route of Module A 3.6--3.8, 7.5,
8.5 and Einstein 19.7. Protocol outputs, metric/matter differentials and
the off-shell exchange current are constructed from one original action.
Covariant native symmetry curves and Hadamard/LF regularity are explicit
geometric/analytic hypotheses; no stress tensor, Ward identity, conservation
or gravitational field equation is assumed. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open Filter TopologicalSpace
open scoped Topology

variable {Ω : Opens (Fin 4 → ℝ)}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev NativeMatterProbe (Ω : Opens (Fin 4 → ℝ)) (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F] := TestFunction Ω F (⊤ : ℕ∞)

def nativeMetricRestrictedAction (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (h : MetricSourceProbe Ω) : ℝ := S (h,0)

def nativeMatterRestrictedAction (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (k : NativeMatterProbe Ω F) : ℝ := S (0,k)

theorem native_metric_restricted_action_finite_regular
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) :
    NativeActionFiniteParamDifferentiable (nativeMetricRestrictedAction S) := by
  intro h k
  simpa [nativeMetricRestrictedAction] using regular (h,0) (k,0)

theorem native_matter_restricted_action_finite_regular
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S) :
    NativeActionFiniteParamDifferentiable (nativeMatterRestrictedAction S) := by
  intro h k
  simpa [nativeMatterRestrictedAction] using regular (0,h) (0,k)

theorem native_metric_restricted_action_hadamard
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionHadamardAtZero S) :
    NativeActionHadamardAtZero (nativeMetricRestrictedAction S) := by
  intro v h hv
  have ht : Tendsto (fun t => (v t,(0 : NativeMatterProbe Ω F))) (𝓝[≠] 0) (𝓝 (h,0)) :=
    hv.prodMk_nhds tendsto_const_nhds
  simpa [nativeMetricRestrictedAction,nativeActionDirectional] using regular _ (h,0) ht

def nativeTestActionFunctional {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (S : TestFunction Ω B (⊤ : ℕ∞) → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S)
    (lf : ∀ (K : Compacts (Fin 4 → ℝ)) (hK : (K : Set (Fin 4 → ℝ)) ⊆ Ω),
      Continuous (nativeActionDirectional S ∘ TestFunction.ofSupportedIn hK)) :
    TestFunction Ω B (⊤ : ℕ∞) →L[ℝ] ℝ :=
  TestFunction.mkCLM ℝ (nativeActionDirectional S)
    (native_action_directional_add S regular) (native_action_directional_smul S regular) lf

theorem native_joint_action_first_variation_split
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S)
    (h : MetricSourceProbe Ω) (k : NativeMatterProbe Ω F) :
    nativeActionDirectional S (h,k) =
      nativeActionDirectional (nativeMetricRestrictedAction S) h +
      nativeActionDirectional (nativeMatterRestrictedAction S) k := by
  have hadd := native_action_directional_add S regular (h,0) (0,k)
  simpa [nativeActionDirectional,nativeMetricRestrictedAction,nativeMatterRestrictedAction] using hadd

theorem native_covariant_action_off_shell_noether
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (g : MetricField) (hg : SmoothCoordinateMetric g)
    (matterLie : CoordinateVectorProbe Ω →L[ℝ] NativeMatterProbe Ω F)
    (symmetryCurve : CoordinateVectorProbe Ω → NativeActionCurve (MetricSourceProbe Ω × NativeMatterProbe Ω F))
    (native_tangent : ∀ X, (symmetryCurve X).tangent = (compactMetricLieCLM Ω g hg X,matterLie X))
    (covariant : ∀ X, (fun t => S ((symmetryCurve X).curve t)) =ᶠ[𝓝 0] fun _ => S 0)
    (X : CoordinateVectorProbe Ω) :
    nativeActionDirectional (nativeMetricRestrictedAction S) (compactMetricLieCLM Ω g hg X) +
      nativeActionDirectional (nativeMatterRestrictedAction S) (matterLie X) = 0 := by
  have hd := native_action_hadamard_curve_derivative S hadamard (symmetryCurve X)
  have hz : HasDerivAt (fun t => S ((symmetryCurve X).curve t)) 0 0 :=
    (hasDerivAt_const (0:ℝ) (S 0)).congr_of_eventuallyEq (covariant X)
  have h := hd.unique hz
  rw [native_tangent,native_joint_action_first_variation_split S regular] at h
  exact h

/-- The total source's off-shell divergence is constructed from the original
matter first variation applied to its native diffeomorphism tangent. -/
theorem native_action_source_off_shell_divergence
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (metricLF : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional (nativeMetricRestrictedAction S) ∘ TestFunction.ofSupportedIn hK))
    (matterLF : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional (nativeMatterRestrictedAction S) ∘ TestFunction.ofSupportedIn hK))
    (g : MetricField) (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (matterLie : CoordinateVectorProbe Ω →L[ℝ] NativeMatterProbe Ω F)
    (symmetryCurve : CoordinateVectorProbe Ω → NativeActionCurve (MetricSourceProbe Ω × NativeMatterProbe Ω F))
    (native_tangent : ∀ X, (symmetryCurve X).tangent = (compactMetricLieCLM Ω g hg X,matterLie X))
    (covariant : ∀ X, (fun t => S ((symmetryCurve X).curve t)) =ᶠ[𝓝 0] fun _ => S 0) :
    constructedSourceDivergence Ω g hg
      (representedMetricSource (nativeTestActionFunctional (nativeMetricRestrictedAction S)
        (native_metric_restricted_action_finite_regular S regular) metricLF)) =
      (nativeTestActionFunctional (nativeMatterRestrictedAction S)
        (native_matter_restricted_action_finite_regular S regular) matterLF).comp matterLie := by
  apply (constructed_source_ward_iff_divergence Ω g hg symmetric _ _).mp
  intro X
  have h := native_covariant_action_off_shell_noether S regular hadamard g hg matterLie
    symmetryCurve native_tangent covariant X
  change nativeActionDirectional (nativeMetricRestrictedAction S) (compactMetricLieCLM Ω g hg X) =
    -nativeActionDirectional (nativeMatterRestrictedAction S) (matterLie X)
  linarith

theorem native_action_internal_equations_imply_closed_source
    (S : MetricSourceProbe Ω × NativeMatterProbe Ω F → ℝ)
    (regular : NativeActionFiniteParamDifferentiable S)
    (hadamard : NativeActionHadamardAtZero S)
    (metricLF : ∀ (K : Compacts CoordinatePoint) (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (nativeActionDirectional (nativeMetricRestrictedAction S) ∘ TestFunction.ofSupportedIn hK))
    (g : MetricField) (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (matterLie : CoordinateVectorProbe Ω →L[ℝ] NativeMatterProbe Ω F)
    (symmetryCurve : CoordinateVectorProbe Ω → NativeActionCurve (MetricSourceProbe Ω × NativeMatterProbe Ω F))
    (native_tangent : ∀ X, (symmetryCurve X).tangent = (compactMetricLieCLM Ω g hg X,matterLie X))
    (covariant : ∀ X, (fun t => S ((symmetryCurve X).curve t)) =ᶠ[𝓝 0] fun _ => S 0)
    (internal_equations : ∀ k, nativeActionDirectional (nativeMatterRestrictedAction S) k=0) :
    constructedSourceDivergence Ω g hg
      (representedMetricSource (nativeTestActionFunctional (nativeMetricRestrictedAction S)
        (native_metric_restricted_action_finite_regular S regular) metricLF)) = 0 := by
  apply (constructed_source_closed_ward_iff Ω g hg symmetric _).mp
  intro X
  have h := native_covariant_action_off_shell_noether S regular hadamard g hg matterLie
    symmetryCurve native_tangent covariant X
  rw [internal_equations] at h
  simpa only [add_zero] using h

#print axioms native_metric_restricted_action_finite_regular
#print axioms native_matter_restricted_action_finite_regular
#print axioms native_metric_restricted_action_hadamard
#print axioms nativeTestActionFunctional
#print axioms native_joint_action_first_variation_split
#print axioms native_covariant_action_off_shell_noether
#print axioms native_action_source_off_shell_divergence
#print axioms native_action_internal_equations_imply_closed_source
end
end AASCSemanticExhaustion
