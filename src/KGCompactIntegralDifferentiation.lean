import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
set_option maxHeartbeats 600000
open Set MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon

/-- The concrete compact-support criterion used for localized energy integrals. -/
theorem compactSupport_of_zero_outside_compact
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {f : E → ℝ} {K : Set E} (hK : IsCompact K)
    (hf : ∀ x, x ∉ K → f x=0) : HasCompactSupport f := by
  apply hK.of_isClosed_subset (isClosed_tsupport f)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (hf x hn)

/-- A local uniform compact spatial support and joint continuity produce the actual
integrable derivative bound; no differentiation-under-integral certificate is assumed. -/
theorem compactIntegral_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (F F' : ℝ → E → ℝ) (t₀ : ℝ) (K : Set E) (hK : IsCompact K)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hsupport : ∀ t ∈ Icc (t₀-1) (t₀+1), ∀ x, x ∉ K → F t x=0 ∧ F' t x=0)
    (hd : ∀ x, ∀ t ∈ Ioo (t₀-1) (t₀+1), HasDerivAt (fun s => F s x) (F' t x) t) :
    HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, F' t₀ x ∂μ) t₀ := by
  have ht : t₀ ∈ Icc (t₀-1) (t₀+1) := by constructor <;> linarith
  have hf0 : HasCompactSupport (F t₀) := compactSupport_of_zero_outside_compact hK
    (fun x hx => (hsupport t₀ ht x hx).1)
  have hcF (t : ℝ) : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hcF' (t : ℝ) : Continuous (F' t) := hF'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (t₀-1) (t₀+1))).prod hK).exists_bound_of_continuousOn hF'.continuousOn
  have hb : Integrable (K.indicator (fun _ : E => C)) μ :=
    (integrableOn_const (hK.measure_ne_top (μ := μ))).integrable_indicator hK.measurableSet
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : t₀-1<t₀) (by linarith : t₀<t₀+1))
    (Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
    ((hcF t₀).integrable_of_hasCompactSupport hf0)
    (hcF' t₀).aestronglyMeasurable ?_ hb (Eventually.of_forall hd)).2
  exact Eventually.of_forall fun x t hti => by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact hC (t,x) ⟨⟨hti.1.le,hti.2.le⟩,hx⟩
    · rw [indicator_of_notMem hx,(hsupport t ⟨hti.1.le,hti.2.le⟩ x hx).2,norm_zero]

end AASCKleinGordon
