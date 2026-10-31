import NativeComparisonFrameTransport
import NativeScalarClockMetricAction

/-! A connected calibrated comparison -> constructed metric -> actual action
derivative -> source theorem. There is no background-metric argument. Original
comparison records, affine dimension, quadratic receiving scope, and the chosen
scalar law remain explicit branch inputs. This is not full original Sigma or
general Einstein equation-form attachment. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open AASCMetricConstruction TopologicalSpace

def nativeComparisonConstructedMetric (r : OriginalComparisonAnswers) : MetricField :=
  fun _=> -reconstructComparison r

theorem native_comparison_constructed_metric_recovers_original_answers
    (r : OriginalComparisonAnswers) (p : CoordinatePoint) :
    comparisonAnswers (-nativeComparisonConstructedMetric r p)=r := by
  simpa only [nativeComparisonConstructedMetric,neg_neg] using
    comparison_reconstruction_preserves_all_original_answers r

theorem native_comparison_constructed_metric_symmetric (r : OriginalComparisonAnswers) :
    MetricFieldSymmetric (nativeComparisonConstructedMetric r) := by
  intro p a b
  exact congrArg Neg.neg
    (congrArg (fun M:ComparisonMatrix=>M a b) (reconstruct_comparison_symmetric r)).symm

theorem native_comparison_constructed_metric_continuous (r : OriginalComparisonAnswers) :
    Continuous (nativeComparisonConstructedMetric r) := continuous_const

theorem native_comparison_constructed_metric_nondegenerate
    (r : OriginalComparisonAnswers) (null : ∀ i:Fin 10,i≠0 → r i=0)
    (clock : 0<r 0) (p : CoordinatePoint) :
    (nativeComparisonConstructedMetric r p).det≠0 := by
  have hm:(reconstructComparison r).det≠0:=by
    rw [constructed_null_receipt_determinant _ null]
    exact neg_ne_zero.mpr (pow_ne_zero _ (ne_of_gt clock))
  simpa [nativeComparisonConstructedMetric,Matrix.det_neg] using hm

theorem native_original_comparisons_construct_metric_and_actual_scalar_source
    {Ω : Opens CoordinatePoint} (r : OriginalComparisonAnswers)
    (null : ∀ i:Fin 10,i≠0 → r i=0) (clock : 0<r 0)
    (χ : CoordinatePoint → ℝ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) :
    (∀ p,comparisonAnswers (-nativeComparisonConstructedMetric r p)=r) ∧
    (∀ p,(nativeComparisonConstructedMetric r p).det≠0) ∧
    ∃! T:SymmetricSourceComponents Ω,∀ h,
      (1/2:ℝ)*metricSourcePairing T h=
        nativeActionDirectional
          (nativeScalarClockRelativeAction (nativeComparisonConstructedMetric r) χ μ) h := by
  refine ⟨native_comparison_constructed_metric_recovers_original_answers r,
    native_comparison_constructed_metric_nondegenerate r null clock,?_⟩
  exact native_scalar_clock_actual_action_source_attachment _
    (native_comparison_constructed_metric_symmetric r) χ μ
    (native_comparison_constructed_metric_continuous r) hχ
    (fun p _=>native_comparison_constructed_metric_nondegenerate r null clock p)

#print axioms native_comparison_constructed_metric_recovers_original_answers
#print axioms native_comparison_constructed_metric_symmetric
#print axioms native_comparison_constructed_metric_continuous
#print axioms native_comparison_constructed_metric_nondegenerate
#print axioms native_original_comparisons_construct_metric_and_actual_scalar_source
end
end AASCSemanticExhaustion
