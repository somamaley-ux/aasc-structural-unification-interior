import SRConeRefinementAttachment
import NativeComparisonConstructedActionSource
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Full original cone/isotropy construction -> actual nondegenerate matrix
metric -> actual scalar relative-action derivative -> unique distribution.
Finite comparison reconstruction is used only after the full form exists.
No background metric, metric-existence or stress/conservation field is input. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open AASCMetricConstruction TopologicalSpace
open scoped Matrix

variable (τ : CoordinatePoint →L[ℝ] ℝ) [Nontrivial (SRClockSpatialSpace τ)]
  (e : CoordinatePoint) (clockOne : τ e=1) {H : Type}

def srSourceConstructedMetric (s : SRStructuralConeSource τ e H) : MetricField:=
  fun _=> -(srSourceLorentzForm τ e clockOne s).toMatrix'

theorem sr_full_cone_constructed_matrix_is_symmetric (s : SRStructuralConeSource τ e H) :
    ((srSourceLorentzForm τ e clockOne s).toMatrix').transpose=
      (srSourceLorentzForm τ e clockOne s).toMatrix' :=
  (srSourceLorentzForm τ e clockOne s).isSymm_toMatrix'

theorem sr_full_cone_constructed_matrix_det_ne_zero (s : SRStructuralConeSource τ e H) :
    (srSourceLorentzForm τ e clockOne s).toMatrix'.det≠0 := by
  have hs:=sr_source_constructed_lorentz_nondegenerate τ e clockOne s
  have hm:=LinearMap.BilinForm.SeparatingLeft.toMatrix' hs
  exact Matrix.separatingLeft_iff_det_ne_zero.mp hm

theorem sr_full_cone_constructed_matrix_has_its_derived_finite_comparison_receipt
    (s : SRStructuralConeSource τ e H) :
    reconstructComparison (comparisonAnswers (srSourceLorentzForm τ e clockOne s).toMatrix')=
      (srSourceLorentzForm τ e clockOne s).toMatrix' :=
  comparison_reconstruction_recovers_every_symmetric_receipt _
    (sr_full_cone_constructed_matrix_is_symmetric τ e clockOne s)

theorem sr_full_cone_constructed_metric_symmetric (s : SRStructuralConeSource τ e H) :
    MetricFieldSymmetric (srSourceConstructedMetric τ e clockOne s) := by
  intro p a b
  exact congrArg Neg.neg
    (congrArg (fun M:ComparisonMatrix=>M a b)
      (sr_full_cone_constructed_matrix_is_symmetric τ e clockOne s)).symm

theorem sr_full_cone_constructed_metric_nondegenerate (s : SRStructuralConeSource τ e H)
    (p : CoordinatePoint) : (srSourceConstructedMetric τ e clockOne s p).det≠0 := by
  simpa [srSourceConstructedMetric,Matrix.det_neg] using
    sr_full_cone_constructed_matrix_det_ne_zero τ e clockOne s

theorem sr_full_original_cone_constructs_actual_scalar_action_and_unique_source
    {Ω : Opens CoordinatePoint} (s : SRStructuralConeSource τ e H)
    (χ : CoordinatePoint → ℝ) (hχ : ContDiff ℝ 2 χ) (μ : ℝ) :
    (∀ p,(srSourceConstructedMetric τ e clockOne s p).det≠0) ∧
      ∃! T:SymmetricSourceComponents Ω,∀ h,
        (1/2:ℝ)*metricSourcePairing T h=
          nativeActionDirectional
            (nativeScalarClockRelativeAction (srSourceConstructedMetric τ e clockOne s) χ μ) h := by
  refine ⟨sr_full_cone_constructed_metric_nondegenerate τ e clockOne s,?_⟩
  exact native_scalar_clock_actual_action_source_attachment _
    (sr_full_cone_constructed_metric_symmetric τ e clockOne s) χ μ continuous_const hχ
    (fun p _=>sr_full_cone_constructed_metric_nondegenerate τ e clockOne s p)

#print axioms sr_full_cone_constructed_matrix_is_symmetric
#print axioms sr_full_cone_constructed_matrix_det_ne_zero
#print axioms sr_full_cone_constructed_matrix_has_its_derived_finite_comparison_receipt
#print axioms sr_full_cone_constructed_metric_symmetric
#print axioms sr_full_cone_constructed_metric_nondegenerate
#print axioms sr_full_original_cone_constructs_actual_scalar_action_and_unique_source
end
end AASCSemanticExhaustion
