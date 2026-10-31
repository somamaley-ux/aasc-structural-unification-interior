import CompactSourceWardConstruction

/-! Assemble the operational relation-to-tensor construction and the actual
coordinate Ward equivalence. Native protocol and source-continuation attachment
are still required; no freely supplied functional or tensor enters this theorem. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace

variable {Ω : Opens CoordinatePoint} {Protocol : Type*}

theorem operational_source_distribution_exists_unique
    (d : OperationalMetricIncidence Ω Protocol)
    (continuous_on_compacts : ∀ (K : Compacts CoordinatePoint)
      (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (operationalMetricResponse d ∘ TestFunction.ofSupportedIn hK)) :
    ∃! T : SymmetricSourceComponents Ω,
      ∀ h π, d.incident h π → (1 / 2 : ℝ) * metricSourcePairing T h = d.output π := by
  let W := operationalMetricFunctional d continuous_on_compacts
  refine ⟨representedMetricSource W, ?_, ?_⟩
  · intro h π hπ
    rw [constructed_metric_source_represents]
    exact operational_response_of_incident d h π hπ
  · intro T hT
    apply constructed_metric_source_unique W T
    intro h
    exact (hT h _ (d.total h).choose_spec).trans rfl

theorem operational_source_ward_distribution_equivalence
    (d : OperationalMetricIncidence Ω Protocol)
    (continuous_on_compacts : ∀ (K : Compacts CoordinatePoint)
      (hK : (K : Set CoordinatePoint) ⊆ Ω),
      Continuous (operationalMetricResponse d ∘ TestFunction.ofSupportedIn hK))
    (g : MetricField) (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (J : CoordinateVectorProbe Ω →L[ℝ] ℝ) :
    (∀ X, operationalMetricResponse d (compactMetricLieCLM Ω g hg X) = -J X) ↔
      constructedSourceDivergence Ω g hg
        (representedMetricSource (operationalMetricFunctional d continuous_on_compacts)) = J :=
  constructed_source_ward_iff_divergence Ω g hg symmetric
    (operationalMetricFunctional d continuous_on_compacts) J

#print axioms operational_source_distribution_exists_unique
#print axioms operational_source_ward_distribution_equivalence
end
end AASCSemanticExhaustion
