import RegularCovariantSourceCurrent
import NormalSourceDensityConversion
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! The actual fundamental lemma for all compact smooth tests, followed by
regular density-current identification. This derives pointwise current zero
from distributional closure; no pointwise divergence bridge is assumed. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open TopologicalSpace MeasureTheory
open scoped BigOperators ContDiff

theorem continuous_scalar_source_tests_separate (Ω : Opens CoordinatePoint)
    (f : CoordinatePoint → ℝ) (hf : Continuous f)
    (zero_tests : ∀ φ : ScalarSourceProbe Ω, (∫ x, f x * φ x)=0) :
    ∀ p∈Ω, f p=0 := by
  have hae : ∀ᵐ x, x∈(Ω:Set CoordinatePoint) → f x=0 :=
    Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrable.locallyIntegrableOn _) (by
        intro ψ hψ hcompact hsupport
        let φ : ScalarSourceProbe Ω := ⟨ψ,hψ,hcompact,hsupport⟩
        simpa only [smul_eq_mul,mul_comm] using zero_tests φ)
  have hr : f =ᵐ[volume.restrict (Ω:Set CoordinatePoint)] (fun _ => 0) :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).mpr hae
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hr Ω.isOpen hf.continuousOn continuousOn_const

def compactVectorTestInsertion (Ω : Opens CoordinatePoint) (e : Fin 4) :
    ScalarSourceProbe Ω →L[ℝ] CoordinateVectorProbe Ω :=
  TestFunction.postcompCLM (ContinuousLinearMap.pi
    (fun j => if j=e then ContinuousLinearMap.id ℝ ℝ else 0))

theorem compact_vector_test_insertion_apply (Ω : Opens CoordinatePoint) (e j : Fin 4)
    (φ : ScalarSourceProbe Ω) (p : CoordinatePoint) :
    compactVectorTestInsertion Ω e φ p j = if j=e then φ p else 0 := by
  by_cases h : j=e <;> simp [compactVectorTestInsertion,TestFunction.postcompCLM_apply,h]

def regularDensityCurrentTerm (g : MetricField) (t : Fin 10 → CoordinatePoint → ℝ)
    (a b e : Fin 4) (p : CoordinatePoint) : ℝ :=
  scalarPartial (fun x => t (sourceSymmetricIndex a b) x * g x b e) p a -
    t (sourceSymmetricIndex a b) p * lowerChristoffel g p b a e

theorem regular_density_current_term_continuous (g : MetricField) (hg : SmoothCoordinateMetric g)
    (t : Fin 10 → CoordinatePoint → ℝ) (ht : ∀ i, ContDiff ℝ 1 (t i)) (a b e : Fin 4) :
    Continuous (regularDensityCurrentTerm g t a b e) :=
  (c1_scalar_partial_continuous _ ((ht _).mul ((hg b e).of_le (by simp))) a).sub
    ((ht _).continuous.mul (smooth_lower_christoffel g hg b a e).continuous)

theorem regular_density_current_scalar_pairing (Ω : Opens CoordinatePoint)
    (g : MetricField) (hg : SmoothCoordinateMetric g) (T : SymmetricSourceComponents Ω)
    (t : Fin 10 → CoordinatePoint → ℝ) (ht : ∀ i, ContDiff ℝ 1 (t i))
    (represents : ∀ i φ, T i φ=∫ x, t i x * φ x)
    (e : Fin 4) (φ : ScalarSourceProbe Ω) :
    constructedSourceDivergence Ω g hg T (compactVectorTestInsertion Ω e φ) =
      ∫ x, classicalTensorDensityCurrent g (fun p a b => t (sourceSymmetricIndex a b) p) x e * φ x := by
  have hi (a b : Fin 4) : Integrable (fun x => regularDensityCurrentTerm g t a b e x * φ x) :=
    regular_source_test_product_integrable Ω _ (regular_density_current_term_continuous g hg t ht a b e) φ
  have hint : (∫ x, ∑ a : Fin 4, ∑ b : Fin 4, regularDensityCurrentTerm g t a b e x * φ x) =
      ∑ a : Fin 4, ∑ b : Fin 4, ∫ x, regularDensityCurrentTerm g t a b e x * φ x := by
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => hi a b))]
    apply Finset.sum_congr rfl
    intro a _
    exact integral_finset_sum _ (fun b _ => hi a b)
  rw [regular_constructed_source_divergence_pairing Ω g hg T t ht represents]
  have hterm (a b j : Fin 4) :
      (∫ x, regularDensityCurrentTerm g t a b j x * compactVectorTestInsertion Ω e φ x j) =
        if j=e then (∫ x, regularDensityCurrentTerm g t a b e x * φ x) else 0 := by
    by_cases h:j=e <;> simp [compact_vector_test_insertion_apply,h]
  change (∑ a : Fin 4, ∑ b : Fin 4, ∑ j : Fin 4,
    ∫ x, regularDensityCurrentTerm g t a b j x * compactVectorTestInsertion Ω e φ x j) = _
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [← hint]
  apply integral_congr_ae
  filter_upwards with x
  simp only [classicalTensorDensityCurrent,regularDensityCurrentTerm,Finset.sum_mul]

theorem regular_distributional_closure_implies_pointwise_density_current
    (Ω : Opens CoordinatePoint) (g : MetricField) (hg : SmoothCoordinateMetric g)
    (T : SymmetricSourceComponents Ω)
    (t : Fin 10 → CoordinatePoint → ℝ) (ht : ∀ i, ContDiff ℝ 1 (t i))
    (represents : ∀ i φ, T i φ=∫ x, t i x * φ x)
    (closed : constructedSourceDivergence Ω g hg T=0) :
    ∀ p∈Ω, ∀ e, classicalTensorDensityCurrent g
      (fun p a b => t (sourceSymmetricIndex a b) p) p e=0 := by
  intro p hp e
  apply continuous_scalar_source_tests_separate Ω _ ?_ ?_ p hp
  · change Continuous (fun x => ∑ a : Fin 4, ∑ b : Fin 4, regularDensityCurrentTerm g t a b e x)
    apply continuous_finset_sum
    intro a _
    apply continuous_finset_sum
    intro b _
    exact regular_density_current_term_continuous g hg t ht a b e
  · intro φ
    rw [← regular_density_current_scalar_pairing Ω g hg T t ht represents e φ,closed]
    rfl

#print axioms continuous_scalar_source_tests_separate
#print axioms compact_vector_test_insertion_apply
#print axioms regular_density_current_term_continuous
#print axioms regular_density_current_scalar_pairing
#print axioms regular_distributional_closure_implies_pointwise_density_current
end
end AASCSemanticExhaustion
