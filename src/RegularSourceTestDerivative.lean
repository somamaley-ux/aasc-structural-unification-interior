import CompactMetricTestOperators
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The actual integral/testing step for regular source components.
The density representation is a regularity certificate, not a conservation
premise. Boundary terms vanish because the actual test has compact support. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace MeasureTheory
open scoped ContDiff

theorem regular_source_test_product_integrable (Ω : Opens CoordinatePoint)
    (t : CoordinatePoint → ℝ) (ht : Continuous t) (φ : ScalarSourceProbe Ω) :
    Integrable (fun x => t x * φ x) :=
  (ht.mul φ.contDiff.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left

theorem regular_source_test_integration_by_parts (Ω : Opens CoordinatePoint)
    (t : CoordinatePoint → ℝ) (ht : ContDiff ℝ 1 t) (φ : ScalarSourceProbe Ω) (a : Fin 4) :
    (∫ x, t x * compactScalarPartialCLM Ω a φ x) =
      -(∫ x, scalarPartial t x a * φ x) := by
  have hd : ContDiff ℝ 0 (fderiv ℝ t) := ht.fderiv_right (by norm_num)
  have hp : Continuous (fun x => scalarPartial t x a) :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1)).continuous.comp hd.continuous)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (regular_source_test_product_integrable Ω _ hp φ)
    (regular_source_test_product_integrable Ω t ht.continuous (compactScalarPartialCLM Ω a φ))
    (regular_source_test_product_integrable Ω t ht.continuous φ)
    (ht.differentiable (by norm_num)) (φ.contDiff.differentiable (by simp))

/-- A represented regular distribution's actual dual partial derivative is
represented by the actual classical partial derivative, with the correct sign. -/
theorem regular_source_dual_partial_representation (Ω : Opens CoordinatePoint)
    (T : ScalarSourceDistribution Ω) (t : CoordinatePoint → ℝ) (ht : ContDiff ℝ 1 t)
    (regular_representation : ∀ φ, T φ = ∫ x, t x * φ x) (a : Fin 4) (φ : ScalarSourceProbe Ω) :
    (-T.comp (compactScalarPartialCLM Ω a)) φ = ∫ x, scalarPartial t x a * φ x := by
  change -T (compactScalarPartialCLM Ω a φ) = _
  rw [regular_representation, regular_source_test_integration_by_parts Ω t ht φ a, neg_neg]

#print axioms regular_source_test_product_integrable
#print axioms regular_source_test_integration_by_parts
#print axioms regular_source_dual_partial_representation
end
end AASCSemanticExhaustion
