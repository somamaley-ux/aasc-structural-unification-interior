import KGWickDensityContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded

/-! Compactness supplies uniform invertibility and a dominating derivative.
No derivative, bound, source or stress-identification certificate is assumed. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory Filter Set
open scoped Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X]

theorem wick_compact_quantum_relative_action_hasDerivAt (m : Measure X) [IsFiniteMeasure m]
    (g h : X → NativeRealMatrix) (D : X → Fin 4 → Fin 4 → ℂ) (M : X → ℂ)
    (hg : Continuous g) (hh : Continuous h) (hD : Continuous D) (hM : Continuous M)
    (nondegenerate : ∀ p,(g p).det ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ p,
      (wickQuantumActionDensity (g p+t • h p) (D p) (M p)-
        wickQuantumActionDensity (g p) (D p) (M p)) ∂m)
      (∫ p,wickQuantumDensityVariation (g p) (h p) (D p) (M p) ∂m) 0 := by
  let G : ℝ × X → NativeRealMatrix := fun z => g z.2+z.1 • h z.2
  have hG : Continuous G := (hg.comp continuous_snd).add
    (continuous_fst.smul (hh.comp continuous_snd))
  let Udet : Set (ℝ × X) := {z | (G z).det ≠ 0}
  have hUdet : IsOpen Udet := isOpen_ne.preimage hG.matrix_det
  have hprod : ({0} : Set ℝ) ×ˢ (univ : Set X) ⊆ Udet := by
    rintro ⟨t,p⟩ ⟨ht,_⟩
    have ht0 : t=0 := ht
    subst t
    simpa [Udet,G] using nondegenerate p
  obtain ⟨U,V,hU,hV,hzero,hall,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) isCompact_univ hUdet hprod
  have hz : (0 : ℝ) ∈ U := hzero (by simp)
  have hnondeg : ∀ t ∈ U,∀ p,(g p+t • h p).det ≠ 0 := by
    intro t ht p
    exact hUV (show (t,p) ∈ U ×ˢ V from ⟨ht,hall (mem_univ p)⟩)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU 0 hz
  let S : Set ℝ := Metric.closedBall 0 (r/2)
  have hSU : S ⊆ U := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hS : S ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 (by linarith)
  have hc : IsCompact (S ×ˢ (univ : Set X)) :=
    (isCompact_closedBall (0 : ℝ) (r/2)).prod isCompact_univ
  let F : ℝ → X → ℂ := fun t p => wickQuantumActionDensity (g p+t • h p) (D p) (M p)-
    wickQuantumActionDensity (g p) (D p) (M p)
  let F' : ℝ → X → ℂ := fun t p => wickQuantumDensityVariation (g p+t • h p) (h p) (D p) (M p)
  have hcontF' : ContinuousOn (fun z : ℝ × X => F' z.1 z.2) (S ×ˢ (univ : Set X)) := by
    intro z hzS
    exact (wick_quantum_variation_continuousAt G (h ∘ Prod.snd) (D ∘ Prod.snd)
      (M ∘ Prod.snd) hG.continuousAt (hh.comp continuous_snd).continuousAt
      (hD.comp continuous_snd).continuousAt (hM.comp continuous_snd).continuousAt
      (hnondeg z.1 (hSU hzS.1) z.2)).continuousWithinAt
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn (f := fun z : ℝ × X => F' z.1 z.2) hcontF'
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),AEStronglyMeasurable (F t) m := by
    filter_upwards [hU.mem_nhds hz] with t ht
    have hgt : Continuous (fun p => g p+t • h p) := hg.add (continuous_const.smul hh)
    have hf : Continuous (F t) := continuous_iff_continuousAt.2 (by
      intro p
      exact (wick_quantum_density_continuousAt _ D M hgt.continuousAt hD.continuousAt hM.continuousAt
        (hnondeg t ht p)).sub
          (wick_quantum_density_continuousAt g D M hg.continuousAt hD.continuousAt hM.continuousAt
            (nondegenerate p)))
    exact hf.aestronglyMeasurable
  have hint : Integrable (F 0) m := by
    simpa [F] using (integrable_zero X ℂ m)
  have hmeas' : AEStronglyMeasurable (F' 0) m := by
    have hf : Continuous (fun p => wickQuantumDensityVariation (g p) (h p) (D p) (M p)) :=
      continuous_iff_continuousAt.2 (by
        intro p
        exact wick_quantum_variation_continuousAt g h D M hg.continuousAt hh.continuousAt
          hD.continuousAt hM.continuousAt (nondegenerate p))
    simpa [F'] using hf.aestronglyMeasurable (μ := m)
  have hbound : ∀ᵐ p ∂m,∀ t ∈ S,‖F' t p‖ ≤ C := Eventually.of_forall (by
    intro p t ht
    exact hC (t,p) ⟨ht,mem_univ p⟩)
  have hdiff : ∀ᵐ p ∂m,∀ t ∈ S,HasDerivAt (fun r => F r p) (F' t p) t := Eventually.of_forall (by
    intro p t ht
    exact (wick_quantum_density_path_derivative_at (g p) (h p) (D p) (M p) t
      (hnondeg t (hSU ht) p)).sub_const _)
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hmeas hint hmeas' hbound
    (integrable_const C) hdiff
  simpa [F,F'] using result.2

end AASCKleinGordon
