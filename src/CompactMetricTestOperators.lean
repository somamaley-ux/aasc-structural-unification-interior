import CompactMetricSourceRepresentation
import CompactTestMultiplier
import CoordinateMetricLieDerivative

namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace
open scoped BigOperators ContDiff

abbrev CoordinateVectorProbe (Ω : Opens CoordinatePoint) := TestFunction Ω CoordinatePoint (⊤ : ℕ∞)
def SmoothCoordinateMetric (g : MetricField) : Prop := ∀ a b, ContDiff ℝ (∞) (fun x => g x a b)

def compactScalarPartialCLM (Ω : Opens CoordinatePoint) (a : Fin 4) :
    ScalarSourceProbe Ω →L[ℝ] ScalarSourceProbe Ω :=
  (TestFunction.postcompCLM (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1))).comp
    (compactTestFDerivCLM Ω)

def compactVectorComponentCLM (Ω : Opens CoordinatePoint) (e : Fin 4) :
    CoordinateVectorProbe Ω →L[ℝ] ScalarSourceProbe Ω :=
  TestFunction.postcompCLM (ContinuousLinearMap.proj e)

theorem compact_scalar_partial_apply (Ω : Opens CoordinatePoint) (a : Fin 4)
    (φ : ScalarSourceProbe Ω) (p : CoordinatePoint) :
    compactScalarPartialCLM Ω a φ p = scalarPartial φ p a := rfl

theorem scalar_source_test_sum_apply {Ω : Opens CoordinatePoint} {ι : Type*}
    (s : Finset ι) (f : ι → ScalarSourceProbe Ω) (p : CoordinatePoint) :
    (∑ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  change (TestFunction.coeFnAddMonoidHom Ω ℝ (⊤ : ℕ∞) (∑ i ∈ s, f i)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  rfl

theorem smooth_metric_partial (g : MetricField) (hg : SmoothCoordinateMetric g) (a b c : Fin 4) :
    ContDiff ℝ (∞) (fun x => metricPartial g x a b c) := by
  have hd : ContDiff ℝ (∞) (fderiv ℝ (fun x => g x a b)) :=
    (hg a b).fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single c 1)).contDiff.comp hd

theorem smooth_lower_christoffel (g : MetricField) (hg : SmoothCoordinateMetric g) (a b c : Fin 4) :
    ContDiff ℝ (∞) (fun x => lowerChristoffel g x a b c) :=
  contDiff_const.mul (((smooth_metric_partial g hg a c b).add
    (smooth_metric_partial g hg a b c)).sub (smooth_metric_partial g hg b c a))

/-- This contains the actual first derivatives of the metric and vector test. -/
def compactMetricLieComponentCLM (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (a b : Fin 4) :
    CoordinateVectorProbe Ω →L[ℝ] ScalarSourceProbe Ω :=
  ∑ e : Fin 4,
    (((compactTestMulCLM Ω (fun x => metricPartial g x a b e) (smooth_metric_partial g hg a b e)).comp
      (compactVectorComponentCLM Ω e)) +
    ((compactTestMulCLM Ω (fun x => g x e b) (hg e b)).comp
      ((compactScalarPartialCLM Ω a).comp (compactVectorComponentCLM Ω e))) +
    ((compactTestMulCLM Ω (fun x => g x a e) (hg a e)).comp
      ((compactScalarPartialCLM Ω b).comp (compactVectorComponentCLM Ω e))))

theorem compact_metric_lie_component_apply (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (a b : Fin 4) (X : CoordinateVectorProbe Ω) (p : CoordinatePoint) :
    compactMetricLieComponentCLM Ω g hg a b X p = coordinateMetricLieDerivative g X p a b := by
  simp only [compactMetricLieComponentCLM, ContinuousLinearMap.sum_apply]
  rw [scalar_source_test_sum_apply]
  rfl

/-- The actual covariant derivative of the metric-lowered vector has this
first-order form; no inverse coefficients need extension outside the chart. -/
def compactCovariantGradientComponentCLM (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (a b : Fin 4) :
    CoordinateVectorProbe Ω →L[ℝ] ScalarSourceProbe Ω :=
  ∑ e : Fin 4,
    (((compactTestMulCLM Ω (fun x => g x b e) (hg b e)).comp
      ((compactScalarPartialCLM Ω a).comp (compactVectorComponentCLM Ω e))) +
    ((compactTestMulCLM Ω (fun x => lowerChristoffel g x b a e) (smooth_lower_christoffel g hg b a e)).comp
      (compactVectorComponentCLM Ω e)))

theorem compact_covariant_gradient_component_apply (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (a b : Fin 4) (X : CoordinateVectorProbe Ω) (p : CoordinatePoint) :
    compactCovariantGradientComponentCLM Ω g hg a b X p =
      ∑ e : Fin 4, (g p b e * scalarPartial (fun x => X x e) p a + lowerChristoffel g p b a e * X p e) := by
  simp only [compactCovariantGradientComponentCLM, ContinuousLinearMap.sum_apply]
  rw [scalar_source_test_sum_apply]
  rfl

theorem compact_lie_eq_covariant_gradient_operators (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g) (a b : Fin 4) :
    compactMetricLieComponentCLM Ω g hg a b =
      compactCovariantGradientComponentCLM Ω g hg a b +
        compactCovariantGradientComponentCLM Ω g hg b a := by
  apply ContinuousLinearMap.ext
  intro X
  apply TestFunction.ext
  intro p
  rw [compact_metric_lie_component_apply]
  change _ = compactCovariantGradientComponentCLM Ω g hg a b X p +
    compactCovariantGradientComponentCLM Ω g hg b a X p
  rw [compact_covariant_gradient_component_apply, compact_covariant_gradient_component_apply]
  unfold coordinateMetricLieDerivative
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hc := lowerChristoffel_metric_compatibility g symmetric p a b e
  rw [hc, lowerChristoffel_torsion_free g symmetric p a e b,
    lowerChristoffel_torsion_free g symmetric p b e a, symmetric p e b]
  ring

#print axioms compact_scalar_partial_apply
#print axioms scalar_source_test_sum_apply
#print axioms smooth_metric_partial
#print axioms smooth_lower_christoffel
#print axioms compact_metric_lie_component_apply
#print axioms compact_covariant_gradient_component_apply
#print axioms compact_lie_eq_covariant_gradient_operators
end
end AASCSemanticExhaustion
