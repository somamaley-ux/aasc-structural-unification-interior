import OriginalEHJetLagrangian
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded

/-! Differentiate the same density over a compact finite-measure carrier.
Uniform determinant sign and derivative domination follow from compactness
and continuity of the actual two-jets; they are not response certificates. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Elementwise

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X]

omit [MeasurableSpace X] [BorelSpace X] [T2Space X] in
theorem eh_compact_jet_negative_near (J H : X → EHMetricJet)
    (hJ : Continuous J) (hH : Continuous H) (negative : ∀ p, (J p).1.det < 0) :
    ∃ U : Set ℝ, IsOpen U ∧ 0 ∈ U ∧ ∀ t ∈ U, ∀ p, (J p + t • H p).1.det < 0 := by
  let A : ℝ × X → EHMetricJet := fun z => J z.2 + z.1 • H z.2
  have hA : Continuous A := (hJ.comp continuous_snd).add
    (continuous_fst.smul (hH.comp continuous_snd))
  let D : Set (ℝ × X) := {z | (A z).1.det < 0}
  have hD : IsOpen D := isOpen_Iio.preimage
    ((eh_jet_determinant_contDiff.continuous).comp hA)
  have inside : ({0} : Set ℝ) ×ˢ (univ : Set X) ⊆ D := by
    rintro ⟨t,p⟩ ⟨ht,_⟩
    have ht0 : t = 0 := ht
    subst t
    simpa [D,A] using negative p
  obtain ⟨U,V,hU,_,hzero,hall,hUV⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : ℝ))) isCompact_univ hD inside
  refine ⟨U,hU,hzero (by simp),?_⟩
  intro t ht p
  exact hUV (show (t,p) ∈ U ×ˢ V from ⟨ht,hall (mem_univ p)⟩)

omit [T2Space X] in
theorem eh_compact_jet_relative_action_hasDerivAt (m : Measure X) [IsFiniteMeasure m]
    (κ Λ : ℝ) (J H : X → EHMetricJet) (hJ : Continuous J) (hH : Continuous H)
    (negative : ∀ p, (J p).1.det < 0) :
    HasDerivAt (fun t : ℝ => ∫ p, (ehJetDensity κ Λ (J p + t • H p) -
      ehJetDensity κ Λ (J p)) ∂m)
      (∫ p, fderiv ℝ (ehJetDensity κ Λ) (J p) (H p) ∂m) 0 := by
  obtain ⟨U,hU,hzero,hn⟩ := eh_compact_jet_negative_near J H hJ hH negative
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU 0 hzero
  let S : Set ℝ := Metric.closedBall 0 (r/2)
  have hSU : S ⊆ U := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hS : S ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 (by linarith)
  have compact : IsCompact (S ×ˢ (univ : Set X)) :=
    (isCompact_closedBall (0 : ℝ) (r/2)).prod isCompact_univ
  let A : ℝ × X → EHMetricJet := fun z => J z.2 + z.1 • H z.2
  have hA : Continuous A := (hJ.comp continuous_snd).add
    (continuous_fst.smul (hH.comp continuous_snd))
  let F : ℝ → X → ℝ := fun t p => ehJetDensity κ Λ (J p + t • H p) - ehJetDensity κ Λ (J p)
  let F' : ℝ → X → ℝ := fun t p => fderiv ℝ (ehJetDensity κ Λ) (J p + t • H p) (H p)
  have derivCont : ContinuousOn (fun z : ℝ × X => F' z.1 z.2) (S ×ˢ (univ : Set X)) := by
    intro z hz
    have hc := eh_jet_density_contDiffAt κ Λ (A z) (hn z.1 (hSU hz.1) z.2)
    exact (((hc.fderiv_right (m := 0) (by simp)).continuousAt.comp hA.continuousAt).clm_apply
      (hH.comp continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := compact.exists_bound_of_continuousOn derivCont
  have meas : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) m := by
    filter_upwards [hU.mem_nhds hzero] with t ht
    have hcont : Continuous (F t) := continuous_iff_continuousAt.mpr (by
      intro p
      have hpath : Continuous (fun q : X => J q + t • H q) := hJ.add (continuous_const.smul hH)
      have varied : ContinuousAt (fun q : X => ehJetDensity κ Λ (J q + t • H q)) p :=
        ContinuousAt.comp (f := fun q : X => J q + t • H q) (x := p)
          (eh_jet_density_contDiffAt κ Λ (J p + t • H p) (hn t ht p)).continuousAt hpath.continuousAt
      have base : ContinuousAt (fun q : X => ehJetDensity κ Λ (J q)) p :=
        (eh_jet_density_contDiffAt κ Λ (J p) (negative p)).continuousAt.comp hJ.continuousAt
      exact varied.sub base)
    exact hcont.aestronglyMeasurable
  have baseInt : Integrable (F 0) m := by
    simp [F]
  have baseMeas : AEStronglyMeasurable (F' 0) m := by
    have hc : Continuous (F' 0) := continuous_iff_continuousAt.mpr (by
      intro p
      have hs := eh_jet_density_contDiffAt κ Λ (J p) (negative p)
      simpa [F'] using (((hs.fderiv_right (m := 0) (by simp)).continuousAt.comp
        hJ.continuousAt).clm_apply hH.continuousAt))
    exact hc.aestronglyMeasurable
  have bound : ∀ᵐ p ∂m, ∀ t ∈ S, ‖F' t p‖ ≤ C := Eventually.of_forall (by
    intro p t ht
    exact hC (t,p) ⟨ht,mem_univ p⟩)
  have diff : ∀ᵐ p ∂m, ∀ t ∈ S, HasDerivAt (fun s => F s p) (F' t p) t :=
    Eventually.of_forall (by
      intro p t ht
      have hp : HasDerivAt (fun s : ℝ => J p + s • H p) (H p) t := by
        simpa using ((hasDerivAt_id t).smul_const (H p)).const_add (J p)
      have hd := ((eh_jet_density_contDiffAt κ Λ _ (hn t (hSU ht) p)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt t hp
      exact hd.sub_const _)
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS meas baseInt baseMeas
    bound (integrable_const C) diff
  simpa [F,F'] using result.2

end
end AASCSemanticExhaustion
