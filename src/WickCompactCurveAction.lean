import WickDensityCurveCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded

/-! Compactness derives a common inverse-metric neighborhood and a uniform
continuous derivative bound for actual C1 curves of the SAME density. -/
noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory Filter Set
open scoped Topology
open AASCSemanticExhaustion
namespace AASCKleinGordon
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X]

theorem wick_compact_quantum_curve_relative_action_hasDerivAt (m : Measure X) [IsFiniteMeasure m]
    (γ γdot : ℝ → X → NativeRealMatrix) (D : X → Fin 4 → Fin 4 → ℂ) (M : X → ℂ)
    (hγ : Continuous (Function.uncurry γ)) (hγdot : Continuous (Function.uncurry γdot))
    (hderiv : ∀ t p, HasDerivAt (fun r => γ r p) (γdot t p) t) (hD : Continuous D) (hM : Continuous M)
    (nondegenerate : ∀ p,(γ 0 p).det ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ p,
      (wickQuantumActionDensity (γ t p) (D p) (M p)-
        wickQuantumActionDensity (γ 0 p) (D p) (M p)) ∂m)
      (∫ p,wickQuantumDensityVariation (γ 0 p) (γdot 0 p) (D p) (M p) ∂m) 0 := by
  let G : ℝ × X → NativeRealMatrix := Function.uncurry γ
  have hG : Continuous G := hγ
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
  have hnondeg : ∀ t ∈ U,∀ p,(γ t p).det ≠ 0 := by
    intro t ht p
    exact hUV (show (t,p) ∈ U ×ˢ V from ⟨ht,hall (mem_univ p)⟩)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU 0 hz
  let S : Set ℝ := Metric.closedBall 0 (r/2)
  have hSU : S ⊆ U := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hS : S ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 (by linarith)
  have hc : IsCompact (S ×ˢ (univ : Set X)) :=
    (isCompact_closedBall (0 : ℝ) (r/2)).prod isCompact_univ
  let F : ℝ → X → ℂ := fun t p => wickQuantumActionDensity (γ t p) (D p) (M p)-
    wickQuantumActionDensity (γ 0 p) (D p) (M p)
  let F' : ℝ → X → ℂ := fun t p => wickQuantumDensityVariation (γ t p) (γdot t p) (D p) (M p)
  have hcontF' : ContinuousOn (fun z : ℝ × X => F' z.1 z.2) (S ×ˢ (univ : Set X)) := by
    intro z hzS
    exact (wick_quantum_variation_continuousAt G (Function.uncurry γdot) (D ∘ Prod.snd)
      (M ∘ Prod.snd) hG.continuousAt hγdot.continuousAt
      (hD.comp continuous_snd).continuousAt (hM.comp continuous_snd).continuousAt
      (hnondeg z.1 (hSU hzS.1) z.2)).continuousWithinAt
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn (f := fun z : ℝ × X => F' z.1 z.2) hcontF'
  have hmeas : ∀ᶠ t in 𝓝 (0 : ℝ),AEStronglyMeasurable (F t) m := by
    filter_upwards [hU.mem_nhds hz] with t ht
    have hgt : Continuous (fun p => γ t p) := hγ.comp (continuous_const.prodMk continuous_id)
    have hf : Continuous (F t) := continuous_iff_continuousAt.2 (by
      intro p
      exact (wick_quantum_density_continuousAt _ D M hgt.continuousAt hD.continuousAt hM.continuousAt
        (hnondeg t ht p)).sub
          (wick_quantum_density_continuousAt (γ 0) D M
            (hγ.comp (continuous_const.prodMk continuous_id)).continuousAt hD.continuousAt hM.continuousAt
            (nondegenerate p)))
    exact hf.aestronglyMeasurable
  have hint : Integrable (F 0) m := by
    simpa only [F,sub_self] using (integrable_zero X ℂ m)
  have hmeas' : AEStronglyMeasurable (F' 0) m := by
    have hf : Continuous (fun p => wickQuantumDensityVariation (γ 0 p) (γdot 0 p) (D p) (M p)) :=
      continuous_iff_continuousAt.2 (by
        intro p
        exact wick_quantum_variation_continuousAt (γ 0) (γdot 0) D M
          (hγ.comp (continuous_const.prodMk continuous_id)).continuousAt
          (hγdot.comp (continuous_const.prodMk continuous_id)).continuousAt
          hD.continuousAt hM.continuousAt (nondegenerate p))
    simpa [F'] using hf.aestronglyMeasurable (μ := m)
  have hbound : ∀ᵐ p ∂m,∀ t ∈ S,‖F' t p‖ ≤ C := Eventually.of_forall (by
    intro p t ht
    exact hC (t,p) ⟨ht,mem_univ p⟩)
  have hdiff : ∀ᵐ p ∂m,∀ t ∈ S,HasDerivAt (fun r => F r p) (F' t p) t := Eventually.of_forall (by
    intro p t ht
    exact (wick_quantum_density_curve_hasDerivAt (fun r => γ r p) t (γdot t p)
      (hderiv t p) (hnondeg t (hSU ht) p) (D p) (M p)).sub_const _)
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hmeas hint hmeas' hbound
    (integrable_const C) hdiff
  simpa [F,F'] using result.2

end AASCKleinGordon
