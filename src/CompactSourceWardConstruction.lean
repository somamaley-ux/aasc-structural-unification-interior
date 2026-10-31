import CompactMetricTestOperators

/-! Construct the actual coordinate distributional Ward interface.
The divergence is the negative full tensor pairing with the constructed
covariant gradient. The Lie-pairing identity is proved, not received as a field.
Native internal equations/exchange and regular-source identification remain
separate from this distributional equivalence. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace
open scoped BigOperators

def sourceSymmetricPair (i : Fin 10) : Fin 4 × Fin 4 :=
  match i.val with
  | 0 => (0,0) | 1 => (0,1) | 2 => (0,2) | 3 => (0,3)
  | 4 => (1,1) | 5 => (1,2) | 6 => (1,3)
  | 7 => (2,2) | 8 => (2,3) | _ => (3,3)

def sourceSymmetricIndex (a b : Fin 4) : Fin 10 :=
  match a.val, b.val with
  | 0,0 => 0 | 0,1 | 1,0 => 1 | 0,2 | 2,0 => 2 | 0,3 | 3,0 => 3
  | 1,1 => 4 | 1,2 | 2,1 => 5 | 1,3 | 3,1 => 6
  | 2,2 => 7 | 2,3 | 3,2 => 8 | _,_ => 9

theorem source_symmetric_index_symmetry (a b : Fin 4) :
    sourceSymmetricIndex a b = sourceSymmetricIndex b a := by
  fin_cases a <;> fin_cases b <;> rfl

def compactMetricLieCLM (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) : CoordinateVectorProbe Ω →L[ℝ] MetricSourceProbe Ω :=
  ∑ i : Fin 10, (sourceTestInsertion i).comp
    (compactMetricLieComponentCLM Ω g hg (sourceSymmetricPair i).1 (sourceSymmetricPair i).2)

theorem compact_metric_lie_projection (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (i : Fin 10) (X : CoordinateVectorProbe Ω) :
    sourceTestProjection i (compactMetricLieCLM Ω g hg X) =
      compactMetricLieComponentCLM Ω g hg (sourceSymmetricPair i).1 (sourceSymmetricPair i).2 X := by
  simp only [compactMetricLieCLM, ContinuousLinearMap.sum_apply, map_sum,
    ContinuousLinearMap.comp_apply, compact_metric_test_projection_insertion]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Negative dual covariant derivative, a continuous functional on genuine
compact smooth vector tests. It includes every ordered tensor entry. -/
def constructedSourceDivergence (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (T : SymmetricSourceComponents Ω) :
    CoordinateVectorProbe Ω →L[ℝ] ℝ :=
  -(∑ a : Fin 4, ∑ b : Fin 4, (T (sourceSymmetricIndex a b)).comp
    (compactCovariantGradientComponentCLM Ω g hg a b))

theorem actual_compact_source_lie_pairing (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (T : SymmetricSourceComponents Ω) (X : CoordinateVectorProbe Ω) :
    (1 / 2 : ℝ) * metricSourcePairing T (compactMetricLieCLM Ω g hg X) =
      -constructedSourceDivergence Ω g hg T X := by
  unfold metricSourcePairing
  simp_rw [compact_metric_lie_projection,
    compact_lie_eq_covariant_gradient_operators Ω g hg symmetric]
  simp only [ContinuousLinearMap.add_apply, map_add, constructedSourceDivergence,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    neg_neg]
  norm_num [Fin.sum_univ_succ, sourceSymmetricPair, sourceSymmetricIndex, symmetricSourceWeight]
  simp only [Fin.ext_iff]
  norm_num [Fin.succ]
  simp only [show (⟨3, by decide⟩ : Fin 4) = 3 from rfl,
    show (⟨3, by decide⟩ : Fin 10) = 3 from rfl,
    show (⟨4, by decide⟩ : Fin 10) = 4 from rfl,
    show (⟨5, by decide⟩ : Fin 10) = 5 from rfl,
    show (⟨6, by decide⟩ : Fin 10) = 6 from rfl,
    show (⟨7, by decide⟩ : Fin 10) = 7 from rfl,
    show (⟨8, by decide⟩ : Fin 10) = 8 from rfl,
    show (⟨9, by decide⟩ : Fin 10) = 9 from rfl]
  ring

/-- Module A 8.2: operational Ward profile iff equality of actual distributions.
This theorem does not receive the old `lie_pairing` bridge. -/
theorem constructed_source_ward_iff_divergence (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) (J : CoordinateVectorProbe Ω →L[ℝ] ℝ) :
    (∀ X, W (compactMetricLieCLM Ω g hg X) = -J X) ↔
      constructedSourceDivergence Ω g hg (representedMetricSource W) = J := by
  have pairing (X : CoordinateVectorProbe Ω) :
      W (compactMetricLieCLM Ω g hg X) =
        -constructedSourceDivergence Ω g hg (representedMetricSource W) X := by
    rw [← constructed_metric_source_represents W]
    exact actual_compact_source_lie_pairing Ω g hg symmetric _ X
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro X
    exact neg_inj.mp ((pairing X).symm.trans (h X))
  · intro h X
    rw [pairing X, h]

theorem constructed_source_closed_ward_iff (Ω : Opens CoordinatePoint) (g : MetricField)
    (hg : SmoothCoordinateMetric g) (symmetric : MetricFieldSymmetric g)
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) :
    (∀ X, W (compactMetricLieCLM Ω g hg X) = 0) ↔
      constructedSourceDivergence Ω g hg (representedMetricSource W) = 0 := by
  simpa using constructed_source_ward_iff_divergence Ω g hg symmetric W 0

#print axioms source_symmetric_index_symmetry
#print axioms compact_metric_lie_projection
#print axioms actual_compact_source_lie_pairing
#print axioms constructed_source_ward_iff_divergence
#print axioms constructed_source_closed_ward_iff
end
end AASCSemanticExhaustion
