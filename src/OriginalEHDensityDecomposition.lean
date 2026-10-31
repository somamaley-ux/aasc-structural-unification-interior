import OriginalEHActualCurrentDerivative
import OriginalEHMetricContractionAlgebra

/-! The actual original-action density variation equals its computed bulk
contraction plus the actual weighted-current divergence. The equality is proved. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

theorem eh_scalar_density_variation_divergence
    (κ Λ : ℝ) (hk : κ ≠ 0) (g h : MetricField)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) :
    ehScalarDensityVariation κ Λ g h p =
      -(coordinateVolumeDensity g p / (2 * κ)) *
        (∑ a : Fin 4, ∑ b : Fin 4,
          ((g p)⁻¹ * (coordinateRicci g p -
            (coordinateScalarCurvature g p / 2) • g p + Λ • g p) *
            (g p)⁻¹) a b * h p a b) +
      ehBoundaryDivergence g h p / (2 * κ) := by
  have hinv := eh_matrix_inverse_variation_contraction (g p)⁻¹ (h p)
    (coordinateRicci g p) (eh_inverse_symmetric g sg p)
  have hs : ehScalarCurvatureVariation g h p =
      -(∑ a : Fin 4, ∑ b : Fin 4,
        ((g p)⁻¹ * coordinateRicci g p * (g p)⁻¹) a b * h p a b) +
      (∑ a : Fin 4, ∑ b : Fin 4, (g p)⁻¹ a b * ehRicciVariation g h p a b) := by
    unfold ehScalarCurvatureVariation ehInverseVariation
    simp only [Finset.sum_add_distrib]
    rw [hinv]
  have ht := eh_matrix_trace_symmetric_contraction (g p)⁻¹ (h p) (sh p)
  have hb := eh_einstein_matrix_contraction (g p)⁻¹ (g p) (coordinateRicci g p) (h p)
    (coordinateScalarCurvature g p) Λ
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_lt negative)))
  have hd := eh_actual_current_divergence_is_ricci_variation g h sg sh hg hh p negative
  unfold ehScalarDensityVariation
  rw [hs,ht,hb,mul_add,← hd]
  field_simp [hk]
  ring

end
end AASCSemanticExhaustion
