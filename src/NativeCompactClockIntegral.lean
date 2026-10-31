import NativeClockDensityContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded

/-! Differentiate the actual relative clock action on a compact integration
carrier. Uniform invertibility and derivative domination are proved from
continuity and compactness; neither is supplied as a certificate field. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X]

theorem native_compact_clock_relative_action_hasDerivAt (m : Measure X) [IsFiniteMeasure m]
    (g h : X → NativeRealMatrix) (v : X → Fin 4 → ℝ) (φ : X → ℝ) (μ : ℝ)
    (hg : Continuous g) (hh : Continuous h) (hv : Continuous v) (hφ : Continuous φ)
    (nondegenerate : ∀ p,(g p).det≠0) :
    HasDerivAt (fun s : ℝ => ∫ p,
      (nativeRealClockDensity (g p+s • h p) (v p) (φ p) μ-
        nativeRealClockDensity (g p) (v p) (φ p) μ) ∂m)
      (∫ p,nativeRealClockMetricVariation (g p) (h p) (v p) (φ p) μ ∂m) 0 := by
  let G : ℝ × X → NativeRealMatrix:=fun z=>g z.2+z.1 • h z.2
  have hG : Continuous G:=(hg.comp continuous_snd).add
    (continuous_fst.smul (hh.comp continuous_snd))
  let D:Set (ℝ × X):={z|(G z).det≠0}
  have hD:IsOpen D:=isOpen_ne.preimage hG.matrix_det
  have hprod : ({0}:Set ℝ) ×ˢ (univ:Set X)⊆D := by
    rintro ⟨s,p⟩ ⟨hs,_⟩
    have hs0:s=0:=hs
    subst s
    simpa [D,G] using nondegenerate p
  obtain ⟨U,V,hU,hV,hzero,hall,hUV⟩:=generalized_tube_lemma
    (isCompact_singleton (x:=(0:ℝ))) isCompact_univ hD hprod
  have hz : (0:ℝ)∈U:=hzero (by simp)
  have hnondeg : ∀ s∈U,∀ p,(g p+s • h p).det≠0:=by
    intro s hs p
    have he:(s,p)∈D:=hUV (show (s,p)∈U ×ˢ V from ⟨hs,hall (mem_univ p)⟩)
    exact he
  obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hU 0 hz
  let S:Set ℝ:=Metric.closedBall 0 (r/2)
  have hSU:S⊆U:=(Metric.closedBall_subset_ball (by linarith)).trans hball
  have hS:S∈𝓝 (0:ℝ):=Metric.closedBall_mem_nhds 0 (by linarith)
  have hc:IsCompact (S ×ˢ (univ:Set X)):=
    (isCompact_closedBall (0:ℝ) (r/2)).prod isCompact_univ
  let F:ℝ → X → ℝ:=fun s p=>nativeRealClockDensity (g p+s • h p) (v p) (φ p) μ-
    nativeRealClockDensity (g p) (v p) (φ p) μ
  let F':ℝ → X → ℝ:=fun s p=>nativeRealClockMetricVariation (g p+s • h p) (h p) (v p) (φ p) μ
  have hcontF' : ContinuousOn (fun z:ℝ × X=>F' z.1 z.2) (S ×ˢ (univ:Set X)):=by
    intro z hzS
    exact (native_clock_variation_continuousAt G (h ∘ Prod.snd) (v ∘ Prod.snd)
      (φ ∘ Prod.snd) μ hG.continuousAt (hh.comp continuous_snd).continuousAt
      (hv.comp continuous_snd).continuousAt (hφ.comp continuous_snd).continuousAt
      (hnondeg z.1 (hSU hzS.1) z.2)).continuousWithinAt
  obtain ⟨C,hC⟩:=hc.exists_bound_of_continuousOn (f:=fun z:ℝ × X=>F' z.1 z.2) hcontF'
  have hmeas : ∀ᶠ s in 𝓝 (0:ℝ),AEStronglyMeasurable (F s) m:=by
    filter_upwards [hU.mem_nhds hz] with s hs
    have hgs:Continuous (fun p=>g p+s • h p):=hg.add (continuous_const.smul hh)
    have hf:Continuous (F s):=continuous_iff_continuousAt.2 (by
      intro p
      exact (native_clock_density_continuousAt _ v φ μ hgs.continuousAt hv.continuousAt hφ.continuousAt
        (hnondeg s hs p)).sub
          (native_clock_density_continuousAt g v φ μ hg.continuousAt hv.continuousAt hφ.continuousAt
            (nondegenerate p)))
    exact hf.aestronglyMeasurable
  have hint:Integrable (F 0) m:=by
    simpa [F] using (integrable_zero X ℝ m)
  have hmeas':AEStronglyMeasurable (F' 0) m:=by
    have hf:Continuous (fun p=>nativeRealClockMetricVariation (g p) (h p) (v p) (φ p) μ):=
      continuous_iff_continuousAt.2 (by
        intro p
        exact native_clock_variation_continuousAt g h v φ μ hg.continuousAt hh.continuousAt
          hv.continuousAt hφ.continuousAt (nondegenerate p))
    simpa [F'] using hf.aestronglyMeasurable (μ:=m)
  have hbound:∀ᵐ p ∂m,∀ s∈S,‖F' s p‖≤C:=Eventually.of_forall (by
    intro p s hs
    exact hC (s,p) ⟨hs,mem_univ p⟩)
  have hdiff:∀ᵐ p ∂m,∀ s∈S,HasDerivAt (fun t=>F t p) (F' s p) s:=Eventually.of_forall (by
    intro p s hs
    exact (native_clock_density_path_derivative_at (g p) (h p) (v p) (φ p) μ s
      (hnondeg s (hSU hs) p)).sub_const _)
  have result:=hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hmeas hint hmeas' hbound
    (integrable_const C) hdiff
  simpa [F,F'] using result.2

#print axioms native_compact_clock_relative_action_hasDerivAt
end
end AASCSemanticExhaustion
