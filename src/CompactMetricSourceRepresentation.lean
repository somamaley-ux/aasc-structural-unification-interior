import OperationalMetricSourceAttachment
import SymmetricTensorCoordinates

/-! Actual ten-component continuous-dual construction on compact smooth tests.
The off-diagonal multiplicity is retained: a full symmetric matrix contraction
counts those entries twice. This is a coordinate tensor-density distribution;
bundle transport and the divergence operator are separate subsequent steps. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
open TopologicalSpace
open scoped BigOperators

abbrev ScalarSourceProbe (Ω : Opens (Fin 4 → ℝ)) := TestFunction Ω ℝ (⊤ : ℕ∞)
abbrev ScalarSourceDistribution (Ω : Opens (Fin 4 → ℝ)) := ScalarSourceProbe Ω →L[ℝ] ℝ
abbrev SymmetricSourceComponents (Ω : Opens (Fin 4 → ℝ)) := Fin 10 → ScalarSourceDistribution Ω

def sourceCoordinateInsertion (i : Fin 10) : ℝ →L[ℝ] (Fin 10 → ℝ) :=
  ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℝ ℝ else 0)

def sourceTestInsertion {Ω : Opens (Fin 4 → ℝ)} (i : Fin 10) :
    ScalarSourceProbe Ω →L[ℝ] MetricSourceProbe Ω :=
  TestFunction.postcompCLM (sourceCoordinateInsertion i)

def sourceTestProjection {Ω : Opens (Fin 4 → ℝ)} (i : Fin 10) :
    MetricSourceProbe Ω →L[ℝ] ScalarSourceProbe Ω :=
  TestFunction.postcompCLM (ContinuousLinearMap.proj i)

theorem compact_metric_test_decomposition {Ω : Opens (Fin 4 → ℝ)} (h : MetricSourceProbe Ω) :
    (∑ i : Fin 10, sourceTestInsertion i (sourceTestProjection i h)) = h := by
  ext x j
  change (TestFunction.coeFnAddMonoidHom Ω (Fin 10 → ℝ) (⊤ : ℕ∞)
    (∑ i : Fin 10, sourceTestInsertion i (sourceTestProjection i h))) x j = h x j
  rw [map_sum]
  simp [sourceTestInsertion, sourceTestProjection, sourceCoordinateInsertion,
    TestFunction.postcompCLM_apply, Function.comp_def, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem compact_metric_test_projection_insertion {Ω : Opens (Fin 4 → ℝ)}
    (i j : Fin 10) (φ : ScalarSourceProbe Ω) :
    sourceTestProjection j (sourceTestInsertion i φ) = if j = i then φ else 0 := by
  ext x
  by_cases h : j = i <;>
    simp [sourceTestInsertion, sourceTestProjection, sourceCoordinateInsertion,
      TestFunction.postcompCLM_apply, Function.comp_def, h]

def symmetricSourceWeight (i : Fin 10) : ℝ :=
  if i = 0 ∨ i = 4 ∨ i = 7 ∨ i = 9 then 1 else 2

theorem symmetric_source_weight_ne_zero (i : Fin 10) : symmetricSourceWeight i ≠ 0 := by
  unfold symmetricSourceWeight
  split <;> norm_num

def representedMetricSource {Ω : Opens (Fin 4 → ℝ)}
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) : SymmetricSourceComponents Ω :=
  fun i => (2 / symmetricSourceWeight i) • W.comp (sourceTestInsertion i)

def metricSourcePairing {Ω : Opens (Fin 4 → ℝ)} (T : SymmetricSourceComponents Ω)
    (h : MetricSourceProbe Ω) : ℝ :=
  ∑ i, symmetricSourceWeight i * T i (sourceTestProjection i h)

theorem constructed_metric_source_represents {Ω : Opens (Fin 4 → ℝ)}
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) (h : MetricSourceProbe Ω) :
    (1 / 2 : ℝ) * metricSourcePairing (representedMetricSource W) h = W h := by
  have term : ∀ i : Fin 10,
      symmetricSourceWeight i * representedMetricSource W i (sourceTestProjection i h) =
        2 * W (sourceTestInsertion i (sourceTestProjection i h)) := by
    intro i
    simp only [representedMetricSource, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    field_simp [symmetric_source_weight_ne_zero i]
  unfold metricSourcePairing
  simp_rw [term]
  rw [← Finset.mul_sum, ← map_sum, compact_metric_test_decomposition]
  ring

theorem metric_source_pairing_insertion {Ω : Opens (Fin 4 → ℝ)}
    (T : SymmetricSourceComponents Ω) (i : Fin 10) (φ : ScalarSourceProbe Ω) :
    metricSourcePairing T (sourceTestInsertion i φ) = symmetricSourceWeight i * T i φ := by
  unfold metricSourcePairing
  simp [compact_metric_test_projection_insertion]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem constructed_metric_source_unique {Ω : Opens (Fin 4 → ℝ)}
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) (T : SymmetricSourceComponents Ω)
    (represents : ∀ h, (1 / 2 : ℝ) * metricSourcePairing T h = W h) :
    T = representedMetricSource W := by
  funext i
  ext φ
  have h := represents (sourceTestInsertion i φ)
  rw [metric_source_pairing_insertion] at h
  simp only [representedMetricSource, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  field_simp [symmetric_source_weight_ne_zero i] at *
  linarith

theorem constructed_metric_source_exists_unique {Ω : Opens (Fin 4 → ℝ)}
    (W : MetricSourceProbe Ω →L[ℝ] ℝ) :
    ∃! T : SymmetricSourceComponents Ω,
      ∀ h, (1 / 2 : ℝ) * metricSourcePairing T h = W h := by
  exact ⟨representedMetricSource W, constructed_metric_source_represents W,
    fun T hT => constructed_metric_source_unique W T hT⟩

/-- Verify that these ten dual coordinates encode the full symmetric contraction,
including the six factors of two, independently of any response functional. -/
theorem symmetric_source_full_matrix_pairing (t h : Fin 10 → ℝ) :
    (∑ a : Fin 4, ∑ b : Fin 4, tensorEncode t a b * tensorEncode h a b) =
      ∑ i : Fin 10, symmetricSourceWeight i * t i * h i := by
  simp [Fin.sum_univ_succ, tensorEncode, symmetricSourceWeight]
  ring

#print axioms compact_metric_test_decomposition
#print axioms compact_metric_test_projection_insertion
#print axioms symmetric_source_weight_ne_zero
#print axioms constructed_metric_source_represents
#print axioms metric_source_pairing_insertion
#print axioms constructed_metric_source_unique
#print axioms constructed_metric_source_exists_unique
#print axioms symmetric_source_full_matrix_pairing
end
end AASCSemanticExhaustion
