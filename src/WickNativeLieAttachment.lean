import WickOriginalGraphStrongAttachment
import ActualCompactSourceLie

/-! Every ACTUAL native compact vector probe maps to the previously proved
Schwartz Lie-test Ward family. Coordinate derivatives and the positive Lie
sign are proved; no represented-Lie equality is assumed. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open TopologicalSpace
open scoped SchwartzMap BigOperators
open AASCSemanticExhaustion
namespace AASCKleinGordon

def wickNativeFlatMetric : MetricField := fun _ => wickFlatMetric

theorem wick_native_flat_smooth : SmoothCoordinateMetric wickNativeFlatMetric :=
  fun _ _ => contDiff_const

theorem wick_native_flat_symmetric : MetricFieldSymmetric wickNativeFlatMetric := by
  intro p i j
  fin_cases i <;> fin_cases j <;> rfl

theorem wick_flat_metric_entry (i j : Fin 4) :
    wickFlatMetric i j = if i=j then wickFlatSign i else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [wickFlatMetric,nativeClockNormalMetric,Matrix.diagonal_apply,wickFlatSign]

def nativeToWickVectorTest (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω)
    (j : Fin 4) : 𝓢(Spacetime,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ wickSpacetimeCoordinates
    (wickCompactTestToSchwartzCLM Ω
      (TestFunction.postcompCLM Complex.ofRealCLM (compactVectorComponentCLM Ω j X)))

theorem native_to_wick_vector_test_apply (Ω : Opens CoordinatePoint)
    (X : CoordinateVectorProbe Ω) (j : Fin 4) (x : Spacetime) :
    nativeToWickVectorTest Ω X j x = (X (wickSpacetimeCoordinates x) j : ℂ) := rfl

theorem wick_spacetime_coordinates_basis (i : Fin 4) :
    wickSpacetimeCoordinates (spacetimeCoordinateVector i) = Pi.single i 1 := by
  rfl

theorem native_to_wick_vector_partial (Ω : Opens CoordinatePoint)
    (X : CoordinateVectorProbe Ω) (i j : Fin 4) (x : Spacetime) :
    fderiv ℝ (nativeToWickVectorTest Ω X j) x (spacetimeCoordinateVector i) =
      (scalarPartial (fun p => X p j) (wickSpacetimeCoordinates x) i : ℂ) := by
  have hf : DifferentiableAt ℝ (fun p => X p j) (wickSpacetimeCoordinates x) :=
    ((compactVectorComponentCLM Ω j X).contDiff.differentiable (by simp)).differentiableAt
  have h := Complex.ofRealCLM.hasFDerivAt.comp x
    (hf.hasFDerivAt.comp x wickSpacetimeCoordinates.hasFDerivAt)
  simp only [Function.comp_def] at h
  change fderiv ℝ (fun y => (X (wickSpacetimeCoordinates y) j : ℂ)) x _ = _
  refine (congrArg (fun L : Spacetime →L[ℝ] ℂ => L (spacetimeCoordinateVector i)) h.fderiv).trans ?_
  change (fderiv ℝ (fun p => X p j) (wickSpacetimeCoordinates x)
    (wickSpacetimeCoordinates (spacetimeCoordinateVector i)) : ℂ) = _
  rw [wick_spacetime_coordinates_basis]
  rfl

theorem wick_native_flat_lie_apply (Ω : Opens CoordinatePoint)
    (X : CoordinateVectorProbe Ω) (p : CoordinatePoint) (i j : Fin 4) :
    coordinateMetricLieDerivative wickNativeFlatMetric X p i j =
      wickFlatSign j * scalarPartial (fun y => X y j) p i +
        wickFlatSign i * scalarPartial (fun y => X y i) p j := by
  simp only [coordinateMetricLieDerivative,wickNativeFlatMetric,metricPartial,wick_flat_metric_entry]
  simp only [ite_mul,zero_mul,Finset.sum_add_distrib]
  simp

theorem native_to_wick_lie_metric_test (Ω : Opens CoordinatePoint)
    (X : CoordinateVectorProbe Ω) :
    nativeToWickMetricTest Ω (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X) =
      wickFlatLieMetricTest (nativeToWickVectorTest Ω X) := by
  funext i j
  apply SchwartzMap.ext
  intro x
  rw [native_to_wick_metric_test_apply,
    compact_source_lie_tensor_is_actual Ω wickNativeFlatMetric wick_native_flat_smooth
      wick_native_flat_symmetric X,wick_native_flat_lie_apply,
    wick_flat_lie_metric_test_apply,native_to_wick_vector_partial,native_to_wick_vector_partial]
  simp only [Complex.ofReal_add,Complex.ofReal_mul]

theorem original_wick_native_lie_full_tensor_ward (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω) :
    originalWickStressMetricDistribution a s u v
      (nativeToWickMetricTest Ω (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X))=0 := by
  rw [native_to_wick_lie_metric_test]
  exact original_wick_flat_lie_test_ward a s u v (nativeToWickVectorTest Ω X)

theorem original_wick_native_lie_half_response_ward (a : Parameters) (s : ℝ)
    (u v : FiniteParticleCore) (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω) :
    originalWickNativeMetricResponse a s u v Ω
      (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)=0 := by
  rw [original_wick_native_metric_response_half_pairing,original_wick_native_lie_full_tensor_ward,mul_zero]

theorem original_wick_native_lie_strong_response_zero (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω) :
    originalWickNativeStrongResponse a s Ω
      (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)=0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro u
  exact original_wick_native_lie_half_response_ward a s u v Ω X

theorem original_wick_native_lie_full_strong_operator_zero (a : Parameters) (s : ℝ)
    (Ω : Opens CoordinatePoint) (X : CoordinateVectorProbe Ω) :
    originalWickNativeFullStressOperator a s Ω
      (compactMetricLieCLM Ω wickNativeFlatMetric wick_native_flat_smooth X)=0 := by
  change originalWickNativeStrongResponse a s Ω _+originalWickNativeStrongResponse a s Ω _=0
  rw [original_wick_native_lie_strong_response_zero,add_zero]

end AASCKleinGordon
