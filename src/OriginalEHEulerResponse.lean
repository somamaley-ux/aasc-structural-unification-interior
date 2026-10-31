import OriginalEHIntegratedBulkVariation

/-! Construct the first-variation functional from its proved original-action
derivative property, then reconstruct its unique symmetric rank-two source.
The Einstein density is an identification theorem, not the definition of E. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory TopologicalSpace
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

variable {Ω : Opens CoordinatePoint}

def EHOriginalFirstVariationProperty (κ Λ : ℝ) (g : MetricField)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) : Prop :=
  ∀ h : MetricSourceProbe Ω,
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ g (t • h)) (W h) 0

theorem eh_original_first_variation_exists_unique (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) :
    ∃! W : MetricSourceProbe Ω →L[ℝ] ℝ, EHOriginalFirstVariationProperty κ Λ g W := by
  have hw : EHOriginalFirstVariationProperty κ Λ g (ehBulkFirstVariationCLM κ Λ g hg negative) := by
    intro h
    rw [eh_bulk_first_variation_clm_integral κ Λ g sg hg negative h]
    exact eh_original_action_bulk_hasDerivAt κ Λ hk g sg hg negative h
  refine ⟨ehBulkFirstVariationCLM κ Λ g hg negative,hw,?_⟩
  intro U hU
  apply ContinuousLinearMap.ext
  intro h
  exact (hU h).unique (hw h)

def originalEHFirstVariation (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) : MetricSourceProbe Ω →L[ℝ] ℝ :=
  Classical.choose (eh_original_first_variation_exists_unique κ Λ hk g sg hg negative).exists

theorem eh_original_first_variation_hasDerivAt (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) :
    EHOriginalFirstVariationProperty κ Λ g (originalEHFirstVariation κ Λ hk g sg hg negative) :=
  Classical.choose_spec (eh_original_first_variation_exists_unique κ Λ hk g sg hg negative).exists

theorem eh_original_first_variation_eq_bulk_clm (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) :
    originalEHFirstVariation κ Λ hk g sg hg negative = ehBulkFirstVariationCLM κ Λ g hg negative := by
  apply ContinuousLinearMap.ext
  intro h
  have actual := eh_original_first_variation_hasDerivAt κ Λ hk g sg hg negative h
  have bulk := eh_original_action_bulk_hasDerivAt κ Λ hk g sg hg negative h
  rw [← eh_bulk_first_variation_clm_integral κ Λ g sg hg negative h] at bulk
  exact actual.unique bulk

def originalEHEulerResponse (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) : SymmetricSourceComponents Ω :=
  representedMetricSource (originalEHFirstVariation κ Λ hk g sg hg negative)

theorem eh_original_euler_response_represents (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    (1/2 : ℝ) * metricSourcePairing (originalEHEulerResponse κ Λ hk g sg hg negative) h =
      originalEHFirstVariation κ Λ hk g sg hg negative h :=
  constructed_metric_source_represents _ h

theorem eh_original_euler_response_regular (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) :
    originalEHEulerResponse κ Λ hk g sg hg negative =
      fun i => nativeRegularScalarDensity (ehComputedSourceDensity κ Λ g i)
        (eh_computed_source_density_locally_integrable κ Λ g hg negative i) := by
  let R : SymmetricSourceComponents Ω := fun i =>
    nativeRegularScalarDensity (ehComputedSourceDensity κ Λ g i)
      (eh_computed_source_density_locally_integrable κ Λ g hg negative i)
  have represents : ∀ h : MetricSourceProbe Ω,
      (1/2 : ℝ) * metricSourcePairing R h = originalEHFirstVariation κ Λ hk g sg hg negative h := by
    intro h
    rw [eh_original_first_variation_eq_bulk_clm κ Λ hk g sg hg negative]
    unfold ehBulkFirstVariationCLM metricSourcePairing
    rw [native_regular_metric_density_integral,Finset.mul_sum]
    change (∑ i : Fin 10, (1/2 : ℝ) *
      (symmetricSourceWeight i * (∫ p, ehComputedSourceDensity κ Λ g i p * h p i))) = _
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact (constructed_metric_source_unique _ R represents).symm

theorem eh_original_action_euler_hasDerivAt (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (h : MetricSourceProbe Ω) :
    HasDerivAt (fun t : ℝ => originalEHRelativeAction κ Λ g (t • h))
      ((1/2 : ℝ) * metricSourcePairing
        (originalEHEulerResponse κ Λ hk g sg hg negative) h) 0 := by
  have hd := eh_original_first_variation_hasDerivAt κ Λ hk g sg hg negative h
  rw [← eh_original_euler_response_represents κ Λ hk g sg hg negative h] at hd
  exact hd

theorem eh_original_euler_response_unique (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (T : SymmetricSourceComponents Ω)
    (represents : ∀ h : MetricSourceProbe Ω, (1/2 : ℝ) * metricSourcePairing T h =
      originalEHFirstVariation κ Λ hk g sg hg negative h) :
    T = originalEHEulerResponse κ Λ hk g sg hg negative :=
  constructed_metric_source_unique _ T represents

theorem eh_original_euler_response_density (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (negative : ∀ p ∈ Ω, (g p).det < 0) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    originalEHEulerResponse κ Λ hk g sg hg negative i φ =
      ∫ p, ehComputedSourceDensity κ Λ g i p * φ p := by
  rw [eh_original_euler_response_regular κ Λ hk g sg hg negative]
  rfl

theorem eh_original_euler_density_full_matrix (κ Λ : ℝ) (hk : κ ≠ 0)
    (g : MetricField) (sg : MetricFieldSymmetric g)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint) :
    tensorEncode (fun i => ehComputedSourceDensity κ Λ g i p) =
      -(coordinateVolumeDensity g p / κ) •
        ((g p)⁻¹ * (coordinateRicci g p -
          (coordinateScalarCurvature g p / 2) • g p + Λ • g p) * (g p)⁻¹) := by
  change tensorEncodeLinear ((2 : ℝ) • tensorDecode (ehComputedBulkDensity κ Λ g p)) = _
  rw [tensorEncodeLinear.map_smul]
  change (2 : ℝ) • tensorEncode (tensorDecode (ehComputedBulkDensity κ Λ g p)) = _
  rw [tensor_encode_decode _ (eh_computed_bulk_density_symmetric κ Λ g sg hg p)]
  unfold ehComputedBulkDensity
  rw [smul_smul]
  congr 1
  field_simp [hk]

end
end AASCSemanticExhaustion
