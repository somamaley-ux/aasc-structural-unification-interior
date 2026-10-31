import OriginalRestrictedEHSource

/-! Public Kernel descent of the actual original EH directional source profile.
The source-role quotient is coarser than the retained history response; its
fibres are not asserted to be global skin. The same action-derived geometric
response represents this source and receives the existing general-envelope
classifier. This does not select a metric, a downstream projection or a
spacetime solution, and does not instantiate the whole original Gravity AER. -/
namespace AASCKleinGordon
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open AASCSemanticExhaustion KGQuantum W9 TopologicalSpace MeasureTheory
open AASC.KernelReference
attribute [local instance] Classical.propDecidable KGInnerCarrier.normed KGInnerCarrier.innerSpace

variable (a : Parameters) (s : ℝ) (Ω : Opens CoordinatePoint)

theorem restricted_eh_sources_exact_original_profiles (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q r : RestrictedOriginalResponse a s Ω) :
    restrictedEHSource a s Ω κ Λ coupling q = restrictedEHSource a s Ω κ Λ coupling r ↔
      ContextualQuotient.Equivalent (restrictedEHObserve a s Ω κ Λ) q r := by
  constructor
  · intro same K
    rw [← restricted_eh_source_half_pairing a s Ω κ Λ coupling q K,
      ← restricted_eh_source_half_pairing a s Ω κ Λ coupling r K, same]
  · intro same
    have functional : restrictedEHVariation a s Ω κ Λ coupling q =
        restrictedEHVariation a s Ω κ Λ coupling r := by
      ext K
      rw [← restricted_eh_observation_is_actual_variation a s Ω κ Λ coupling q K,
        ← restricted_eh_observation_is_actual_variation a s Ω κ Λ coupling r K]
      exact same K
    exact congrArg representedMetricSource functional

theorem restricted_eh_unique_injective_kernel_source (κ Λ : ℝ) (coupling : κ ≠ 0) :
    ∃! reduced : ContextualQuotient.CanonicalQuotient (restrictedEHObserve a s Ω κ Λ) →
        SymmetricSourceComponents Ω,
      (∀ q, reduced (ContextualQuotient.classify (restrictedEHObserve a s Ω κ Λ) q) =
        restrictedEHSource a s Ω κ Λ coupling q) ∧ Function.Injective reduced := by
  obtain ⟨reduced, receipt, unique⟩ := ContextualQuotient.unique_factorization
    (restrictedEHObserve a s Ω κ Λ) (restrictedEHSource a s Ω κ Λ coupling)
    (fun q r same => (restricted_eh_sources_exact_original_profiles a s Ω κ Λ coupling q r).mpr same)
  refine ⟨reduced, ⟨receipt, ?_⟩, ?_⟩
  · intro x y same
    obtain ⟨q, rfl⟩ := ContextualQuotient.classify_surjective (restrictedEHObserve a s Ω κ Λ) x
    obtain ⟨r, rfl⟩ := ContextualQuotient.classify_surjective (restrictedEHObserve a s Ω κ Λ) y
    rw [receipt, receipt] at same
    exact (ContextualQuotient.classify_eq_iff _ q r).mpr
      ((restricted_eh_sources_exact_original_profiles a s Ω κ Λ coupling q r).mp same)
  · intro other agrees
    exact unique other agrees.1

abbrev RestrictedEHKernelProfile (κ Λ : ℝ) :=
  ContextualQuotient.CanonicalQuotient (restrictedEHObserve a s Ω κ Λ)

def restrictedEHKernelSource (κ Λ : ℝ) (coupling : κ ≠ 0) :
    RestrictedEHKernelProfile a s Ω κ Λ → SymmetricSourceComponents Ω :=
  (restricted_eh_unique_injective_kernel_source a s Ω κ Λ coupling).choose

theorem restricted_eh_kernel_source_receipt (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) :
    restrictedEHKernelSource a s Ω κ Λ coupling
      (ContextualQuotient.classify (restrictedEHObserve a s Ω κ Λ) q) =
        restrictedEHSource a s Ω κ Λ coupling q :=
  (restricted_eh_unique_injective_kernel_source a s Ω κ Λ coupling).choose_spec.1.1 q

theorem restricted_eh_kernel_source_injective (κ Λ : ℝ) (coupling : κ ≠ 0) :
    Function.Injective (restrictedEHKernelSource a s Ω κ Λ coupling) :=
  (restricted_eh_unique_injective_kernel_source a s Ω κ Λ coupling).choose_spec.1.2

def restrictedRawEHKernelClass (κ Λ : ℝ) (h : RestrictedRawHistory a Ω) :
    RestrictedEHKernelProfile a s Ω κ Λ :=
  ContextualQuotient.classify (restrictedEHObserve a s Ω κ Λ) (Quotient.mk _ h)

theorem restricted_eh_raw_kernel_profiles_exact (κ Λ : ℝ) (h k : RestrictedRawHistory a Ω) :
    restrictedRawEHKernelClass a s Ω κ Λ h = restrictedRawEHKernelClass a s Ω κ Λ k ↔
      ∀ K, restrictedRawEHObserve a Ω κ Λ h K = restrictedRawEHObserve a Ω κ Λ k K := by
  rw [restrictedRawEHKernelClass, restrictedRawEHKernelClass, ContextualQuotient.classify_eq_iff]
  constructor
  · intro same K
    rw [restricted_eh_raw_observation_square a s Ω, restricted_eh_raw_observation_square a s Ω]
    exact same K
  · intro same K
    rw [← restricted_eh_raw_observation_square a s Ω, ← restricted_eh_raw_observation_square a s Ω]
    exact same K

theorem restricted_eh_raw_kernel_coverage (κ Λ : ℝ) :
    Function.Surjective (restrictedRawEHKernelClass a s Ω κ Λ) := by
  intro q
  obtain ⟨r, rfl⟩ := ContextualQuotient.classify_surjective (restrictedEHObserve a s Ω κ Λ) q
  obtain ⟨h, rfl⟩ := Quotient.exists_rep r
  exact ⟨h, rfl⟩

theorem restricted_eh_source_uses_only_original_metric_operand (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q r : RestrictedOriginalResponse a s Ω)
    (same : (restrictedEHAct a s Ω q).val = (restrictedEHAct a s Ω r).val) :
    restrictedEHSource a s Ω κ Λ coupling q = restrictedEHSource a s Ω κ Λ coupling r := by
  apply (restricted_eh_sources_exact_original_profiles a s Ω κ Λ coupling q r).mpr
  intro K
  unfold restrictedEHObserve
  rw [same]

theorem restricted_eh_kernel_same_metric_representation (κ Λ : ℝ) (coupling : κ ≠ 0)
    (q : RestrictedOriginalResponse a s Ω) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    restrictedEHKernelSource a s Ω κ Λ coupling
      (ContextualQuotient.classify (restrictedEHObserve a s Ω κ Λ) q) i φ =
      ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (restrictedEHMetric a s Ω q)
        (originalEHGeometricResponse κ Λ (restrictedEHMetric a s Ω q))) i p * φ p := by
  rw [restricted_eh_kernel_source_receipt]
  exact restricted_eh_same_metric_source_density a s Ω κ Λ coupling q i φ

/-- The exact six analytic inputs are discharged by the already accepted
action-derived response laws. Canonical source interpretation is the new
same-source connection; classification is reused, not inferred from descent. -/
theorem restricted_original_eh_kernel_einstein_receiving (κ Λ : ℝ) (coupling : κ ≠ 0) :
    (∀ (q : RestrictedOriginalResponse a s Ω) (i : Fin 10) (φ : ScalarSourceProbe Ω),
      restrictedEHKernelSource a s Ω κ Λ coupling
        (ContextualQuotient.classify (restrictedEHObserve a s Ω κ Λ) q) i φ =
        ∫ p, sourceDensityCoordinates (raisedSourceTensorDensity (restrictedEHMetric a s Ω q)
          (originalEHGeometricResponse κ Λ (restrictedEHMetric a s Ω q))) i p * φ p) ∧
    (∃! ac : ℝ × ℝ, ac.1 ≠ 0 ∧
      CoordinateEinsteinResponseForm (originalEHGeometricResponse κ Λ) ac.1 ac.2) := by
  refine ⟨restricted_eh_kernel_same_metric_representation a s Ω κ Λ coupling, ?_⟩
  exact original_curvature_general_response_has_unique_einstein_form _
    (eh_original_geometric_response_regular_natural κ Λ coupling)
    (eh_original_geometric_response_twojet_local κ Λ coupling)
    (eh_original_geometric_curvature_first_response κ Λ coupling)
    (eh_original_geometric_response_symmetric κ Λ coupling)
    (eh_original_geometric_general_closure κ Λ coupling)
    (eh_original_geometric_full_envelope_active κ Λ coupling)

end
end AASCKleinGordon
