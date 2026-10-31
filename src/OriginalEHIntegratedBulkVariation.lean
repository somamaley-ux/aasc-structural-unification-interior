import OriginalEHDensityDecomposition
import OriginalEHComputedBulkDensity

/-! Integrate the proved pointwise decomposition using the accepted actual
current support/IBP theorem. This identifies the original action derivative. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory TopologicalSpace Filter Set
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

def ehComputedBulkPairing (κ Λ : ℝ) (g h : MetricField) (p : CoordinatePoint) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, ehComputedBulkDensity κ Λ g p a b * h p a b

theorem eh_density_decomposition_bulk_pairing (κ Λ : ℝ) (hk : κ ≠ 0) (g h : MetricField)
    (sg : MetricFieldSymmetric g) (sh : MetricFieldSymmetric h)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b))
    (p : CoordinatePoint) (negative : (g p).det < 0) :
    ehScalarDensityVariation κ Λ g h p = ehComputedBulkPairing κ Λ g h p +
      ehBoundaryDivergence g h p / (2*κ) := by
  rw [eh_scalar_density_variation_divergence κ Λ hk g h sg sh hg hh p negative]
  simp only [ehComputedBulkPairing,ehComputedBulkDensity,Matrix.smul_apply,smul_eq_mul,
    Finset.mul_sum,mul_assoc]

variable {Ω : Opens CoordinatePoint}

theorem eh_computed_bulk_probe_pairing (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (h : MetricSourceProbe Ω) (p : CoordinatePoint) :
    ehComputedBulkPairing κ Λ g (ehProbeMetric h) p =
      (1/2 : ℝ) * ∑ i : Fin 10,
        symmetricSourceWeight i * (ehComputedSourceDensity κ Λ g i p * h p i) := by
  have he := tensor_encode_decode (ehComputedBulkDensity κ Λ g p)
    (eh_computed_bulk_density_symmetric κ Λ g sg hg p)
  have hp := symmetric_source_full_matrix_pairing
    (tensorDecode (ehComputedBulkDensity κ Λ g p)) (h p)
  rw [he] at hp
  change (∑ a : Fin 4, ∑ b : Fin 4,
    ehComputedBulkDensity κ Λ g p a b * tensorEncode (h p) a b) = _
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold ehComputedSourceDensity
  ring

theorem eh_computed_density_probe_component_integrable (κ Λ : ℝ) (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) (i : Fin 10) :
    Integrable (fun p => ehComputedSourceDensity κ Λ g i p * h p i) :=
  native_locally_integrable_test_product (ehComputedSourceDensity κ Λ g i)
    (eh_computed_source_density_locally_integrable κ Λ g hg negative i)
    (sourceTestProjection i h)

theorem eh_computed_bulk_probe_integrable (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    Integrable (ehComputedBulkPairing κ Λ g (ehProbeMetric h)) := by
  have hi := (integrable_finset_sum Finset.univ (fun i _ =>
    (eh_computed_density_probe_component_integrable κ Λ g hg negative h i).const_mul
      (symmetricSourceWeight i))).const_mul (1/2 : ℝ)
  convert hi using 1
  funext p
  exact eh_computed_bulk_probe_pairing κ Λ g sg hg h p

theorem eh_computed_bulk_probe_setIntegral (κ Λ : ℝ) (g : MetricField)
    (h : MetricSourceProbe Ω) :
    (∫ p in (Ω : Set CoordinatePoint), ehComputedBulkPairing κ Λ g (ehProbeMetric h) p) =
      ∫ p, ehComputedBulkPairing κ Λ g (ehProbeMetric h) p := by
  rw [← integral_indicator Ω.isOpen.measurableSet]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  by_cases hp : p ∈ Ω
  · simp only [Set.indicator_of_mem hp]
  · have hz : h p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hp (h.tsupport_subset hs))
    have hm : ehProbeMetric h p = 0 := by
      change tensorEncode (h p) = 0
      rw [hz]
      exact tensorEncodeLinear.map_zero
    simp only [Set.indicator_of_notMem hp,ehComputedBulkPairing,hm,Matrix.zero_apply,
      mul_zero,Finset.sum_const_zero]

theorem eh_original_density_variation_integral_bulk (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    (∫ p in (Ω : Set CoordinatePoint), ehScalarDensityVariation κ Λ g (ehProbeMetric h) p) =
      ∫ p, ehComputedBulkPairing κ Λ g (ehProbeMetric h) p := by
  have hb := eh_computed_bulk_probe_integrable κ Λ g sg hg negative h
  have hd := (eh_boundary_divergence_integrable g hg negative h).div_const (2*κ)
  have hs : (fun p => ehScalarDensityVariation κ Λ g (ehProbeMetric h) p) =ᵐ[
      volume.restrict (Ω : Set CoordinatePoint)]
      fun p => ehComputedBulkPairing κ Λ g (ehProbeMetric h) p +
        ehBoundaryDivergence g (ehProbeMetric h) p / (2*κ) := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with p hp
    exact eh_density_decomposition_bulk_pairing κ Λ hk g (ehProbeMetric h) sg
      (eh_probe_metric_symmetric h) hg (eh_probe_metric_smooth h) p (negative p hp)
  rw [integral_congr_ae hs,integral_add hb.integrableOn hd.integrableOn,
    integral_div,eh_boundary_divergence_setIntegral_zero g hg negative h,
    zero_div,add_zero,eh_computed_bulk_probe_setIntegral]

theorem eh_original_action_bulk_hasDerivAt (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ g (t • h))
      (∫ p, ehComputedBulkPairing κ Λ g (ehProbeMetric h) p) 0 := by
  have hd := eh_original_relative_action_hasDerivAt κ Λ g sg hg negative h
  rw [eh_original_density_variation_integral_bulk κ Λ hk g sg hg negative h] at hd
  exact hd

def ehBulkFirstVariationCLM (κ Λ : ℝ) (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  nativeRegularMetricDensity (ehComputedSourceDensity κ Λ g)
    (eh_computed_source_density_locally_integrable κ Λ g hg negative)

theorem eh_bulk_first_variation_clm_integral (κ Λ : ℝ) (g : MetricField)
    (sg : MetricFieldSymmetric g) (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    ehBulkFirstVariationCLM κ Λ g hg negative h =
      ∫ p, ehComputedBulkPairing κ Λ g (ehProbeMetric h) p := by
  have hi (i : Fin 10) := eh_computed_density_probe_component_integrable κ Λ g hg negative h i
  have he : (∫ p, ehComputedBulkPairing κ Λ g (ehProbeMetric h) p) =
      (1/2 : ℝ) * ∑ i : Fin 10, symmetricSourceWeight i *
        (∫ p, ehComputedSourceDensity κ Λ g i p * h p i) := by
    rw [integral_congr_ae (Eventually.of_forall (eh_computed_bulk_probe_pairing κ Λ g sg hg h)),
      integral_const_mul,integral_finset_sum Finset.univ (fun i _ => (hi i).const_mul _)]
    simp_rw [integral_const_mul]
  rw [he]
  unfold ehBulkFirstVariationCLM
  rw [native_regular_metric_density_integral,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end AASCSemanticExhaustion
