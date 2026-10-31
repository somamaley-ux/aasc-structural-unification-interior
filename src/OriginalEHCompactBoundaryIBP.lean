import OriginalEHBoundaryCurrent
import RegularSourceTestDerivative

/-! Ordinary compact integration by parts for the actual original-action
variation current. The pointwise Palatini decomposition is a separate theorem;
it is not assumed here or inferred from this integral cancellation. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter TopologicalSpace Set
open scoped Topology ContDiff BigOperators

variable {Ω : Opens CoordinatePoint}

theorem eh_scalar_test_integrable (φ : ScalarSourceProbe Ω) : Integrable φ :=
  φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport

theorem eh_scalar_test_setIntegral_eq_integral (φ : ScalarSourceProbe Ω) :
    (∫ p in (Ω : Set CoordinatePoint), φ p) = ∫ p, φ p := by
  rw [← integral_indicator Ω.isOpen.measurableSet]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  by_cases hp : p ∈ Ω
  · simp only [Set.indicator_of_mem hp]
  · have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hp (φ.tsupport_subset hs))
    simp only [Set.indicator_of_notMem hp,hz]

theorem eh_scalar_test_partial_integral_zero (φ : ScalarSourceProbe Ω) (c : Fin 4) :
    (∫ p, scalarPartial φ p c) = 0 := by
  have ibp := regular_source_test_integration_by_parts Ω (fun _ => (1 : ℝ)) contDiff_const φ c
  have dc (p : CoordinatePoint) : fderiv ℝ (fun _ : CoordinatePoint => (1 : ℝ)) p = 0 :=
    (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).fderiv
  simpa only [compact_scalar_partial_apply,one_mul,scalarPartial,dc,
    ContinuousLinearMap.zero_apply,zero_mul,integral_zero,neg_zero] using ibp

theorem eh_scalar_test_partial_setIntegral_zero (φ : ScalarSourceProbe Ω) (c : Fin 4) :
    (∫ p in (Ω : Set CoordinatePoint), scalarPartial φ p c) = 0 := by
  change (∫ p in (Ω : Set CoordinatePoint), compactScalarPartialCLM Ω c φ p) = 0
  rw [eh_scalar_test_setIntegral_eq_integral]
  exact eh_scalar_test_partial_integral_zero φ c

def ehBoundaryDivergence (g h : MetricField) (p : CoordinatePoint) : ℝ :=
  ∑ c : Fin 4, scalarPartial (fun q => ehBoundaryCurrent g h q c) p c

theorem eh_boundary_current_component_setIntegral_zero (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) (c : Fin 4) :
    (∫ p in (Ω : Set CoordinatePoint),
      scalarPartial (fun q => ehBoundaryCurrent g (ehProbeMetric h) q c) p c) = 0 :=
  eh_scalar_test_partial_setIntegral_zero (ehBoundaryCurrentTest g hg negative h c) c

theorem eh_boundary_divergence_integrable (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    Integrable (ehBoundaryDivergence g (ehProbeMetric h)) := by
  apply integrable_finset_sum
  intro c _
  exact eh_scalar_test_integrable (compactScalarPartialCLM Ω c
    (ehBoundaryCurrentTest g hg negative h c))

theorem eh_boundary_divergence_setIntegral_zero (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    (∫ p in (Ω : Set CoordinatePoint), ehBoundaryDivergence g (ehProbeMetric h) p) = 0 := by
  unfold ehBoundaryDivergence
  change (∫ p in (Ω : Set CoordinatePoint), ∑ c : Fin 4,
    compactScalarPartialCLM Ω c (ehBoundaryCurrentTest g hg negative h c) p) = 0
  rw [integral_finset_sum Finset.univ (fun c _ =>
    (eh_scalar_test_integrable (compactScalarPartialCLM Ω c
      (ehBoundaryCurrentTest g hg negative h c))).integrableOn)]
  have hz (c : Fin 4) : (∫ p in (Ω : Set CoordinatePoint),
      compactScalarPartialCLM Ω c (ehBoundaryCurrentTest g hg negative h c) p) = 0 :=
    eh_boundary_current_component_setIntegral_zero g hg negative h c
  simp only [hz,Finset.sum_const_zero]

end
end AASCSemanticExhaustion
