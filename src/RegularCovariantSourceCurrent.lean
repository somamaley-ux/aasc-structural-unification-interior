import RegularSourceTestDerivative
import CompactSourceWardConstruction

/-! Actual coordinate current of a C1 tensor-density distribution.
This proves the integral/dual derivative conversion; converting density indices
and volume to the covariant geometric tensor and manifold gluing are separate. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace MeasureTheory
open scoped ContDiff BigOperators

theorem c1_scalar_partial_continuous (t : CoordinatePoint → ℝ) (ht : ContDiff ℝ 1 t) (a : Fin 4) :
    Continuous (fun x => scalarPartial t x a) := by
  have hd : ContDiff ℝ 0 (fderiv ℝ t) := ht.fderiv_right (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single a 1)).continuous.comp hd.continuous

theorem regular_source_multiplier_pairing (Ω : Opens CoordinatePoint)
    (T : ScalarSourceDistribution Ω) (t : CoordinatePoint → ℝ)
    (regular_representation : ∀ φ, T φ = ∫ x, t x * φ x)
    (m : CoordinatePoint → ℝ) (hm : ContDiff ℝ (∞) m) (φ : ScalarSourceProbe Ω) :
    T (compactTestMulCLM Ω m hm φ) = ∫ x, (t x * m x) * φ x := by
  rw [regular_representation]
  apply integral_congr_ae
  filter_upwards with x
  rw [compact_test_multiplier_apply]
  ring

theorem regular_covariant_gradient_component_pairing (Ω : Opens CoordinatePoint)
    (g : MetricField) (hg : SmoothCoordinateMetric g)
    (T : ScalarSourceDistribution Ω) (t : CoordinatePoint → ℝ) (ht : ContDiff ℝ 1 t)
    (regular_representation : ∀ φ, T φ = ∫ x, t x * φ x)
    (a b : Fin 4) (X : CoordinateVectorProbe Ω) :
    -T (compactCovariantGradientComponentCLM Ω g hg a b X) =
      ∑ e : Fin 4, ∫ x,
        (scalarPartial (fun y => t y * g y b e) x a - t x * lowerChristoffel g x b a e) * X x e := by
  simp only [compactCovariantGradientComponentCLM, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.comp_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  let φ := compactVectorComponentCLM Ω e X
  have htg : ContDiff ℝ 1 (fun x => t x * g x b e) := ht.mul ((hg b e).of_le (by simp))
  have hleft := regular_source_test_product_integrable Ω _ (c1_scalar_partial_continuous _ htg a) φ
  have hright := regular_source_test_product_integrable Ω _
    (ht.continuous.mul (smooth_lower_christoffel g hg b a e).continuous) φ
  change Integrable (fun x => (t x * lowerChristoffel g x b a e) * φ x) at hright
  rw [regular_source_multiplier_pairing Ω T t regular_representation,
    regular_source_multiplier_pairing Ω T t regular_representation,
    regular_source_test_integration_by_parts Ω _ htg φ a]
  change -(-(∫ x, scalarPartial (fun y => t y * g y b e) x a * φ x) +
    (∫ x, (t x * lowerChristoffel g x b a e) * φ x)) = _
  rw [neg_add, neg_neg, ← sub_eq_add_neg, ← integral_sub hleft hright]
  apply integral_congr_ae
  filter_upwards with x
  change scalarPartial (fun y => t y * g y b e) x a * φ x -
    (t x * lowerChristoffel g x b a e) * φ x =
    (scalarPartial (fun y => t y * g y b e) x a - t x * lowerChristoffel g x b a e) * φ x
  ring

theorem regular_constructed_source_divergence_pairing (Ω : Opens CoordinatePoint)
    (g : MetricField) (hg : SmoothCoordinateMetric g) (T : SymmetricSourceComponents Ω)
    (t : Fin 10 → CoordinatePoint → ℝ) (ht : ∀ i, ContDiff ℝ 1 (t i))
    (regular_representation : ∀ i φ, T i φ = ∫ x, t i x * φ x)
    (X : CoordinateVectorProbe Ω) :
    constructedSourceDivergence Ω g hg T X =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4, ∫ x,
        (scalarPartial (fun y => t (sourceSymmetricIndex a b) y * g y b e) x a -
          t (sourceSymmetricIndex a b) x * lowerChristoffel g x b a e) * X x e := by
  simp only [constructedSourceDivergence, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  exact regular_covariant_gradient_component_pairing Ω g hg _ _ (ht _)
    (regular_representation _) a b X

#print axioms c1_scalar_partial_continuous
#print axioms regular_source_multiplier_pairing
#print axioms regular_covariant_gradient_component_pairing
#print axioms regular_constructed_source_divergence_pairing
end
end AASCSemanticExhaustion
