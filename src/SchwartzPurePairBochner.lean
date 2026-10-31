import SchwartzJetTranslationContinuity
import SchwartzJetSpanIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon



theorem wick_translate_actual_pair (a : ParticleConfiguration 2) (f g : 𝓢(Momentum,ℂ)) :
    wickSchwartzTranslate a (wickCovariantPairTest f g)=
      wickCovariantPairTest (wickSchwartzTranslate (a 0) f) (wickSchwartzTranslate (a 1) g) := by
  ext z
  simp only [wick_schwartz_translate_apply,wick_covariant_pair_test_apply,Pi.sub_apply]

theorem wick_compact_actual_pair (f g : 𝓢(Momentum,ℂ))
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (wickCovariantPairTest f g) := by
  obtain ⟨R,hR,hr⟩ := hf.isBounded.subset_closedBall_lt 0 (0:Momentum)
  obtain ⟨T,hT,ht⟩ := hg.isBounded.subset_closedBall_lt 0 (0:Momentum)
  apply (isCompact_closedBall (0:ParticleConfiguration 2) (max R T)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  have hn : wickCovariantPairTest f g z≠0 := hz
  rw [wick_covariant_pair_test_apply] at hn
  have hfn : f (z 0)≠0 := by
    intro h
    exact hn (by rw [h,star_zero,zero_mul])
  have hgn : g (z 1)≠0 := (mul_ne_zero_iff.mp hn).2
  have h0 : ‖z 0‖≤R := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hr (subset_closure hfn)
  have h1 : ‖z 1‖≤T := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using ht (subset_closure hgn)
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left hR.le)).mpr
  intro i
  fin_cases i
  · exact h0.trans (le_max_left _ _)
  · exact h1.trans (le_max_right _ _)

def wickPurePairTranslationIntegral (S : Finset (ℕ × ℕ))
    (f g : 𝓢(Momentum,ℂ)) (H : 𝓢(ParticleConfiguration 2,ℂ)) :=
  ∫ a : ParticleConfiguration 2,
    H a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a (wickCovariantPairTest f g))

/-- Integrability is proved for the actual translated pure-pair family. -/
theorem wick_actual_pure_pair_jet_integrable (S : Finset (ℕ × ℕ))
    (f g : 𝓢(Momentum,ℂ)) (H : 𝓢(ParticleConfiguration 2,ℂ))
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hH : HasCompactSupport H) :
    Integrable (fun a : ParticleConfiguration 2 =>
      H a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a (wickCovariantPairTest f g))) :=
  wick_compact_weighted_translate_jet_integrable volume S _ H (wick_compact_actual_pair f g hf hg) hH

/-- The ACTUAL weighted translated-pair integral has finite pure-pair approximants.
No identity between this integral and the original H is asserted here. -/
theorem wick_actual_pure_pair_integral_approximation (S : Finset (ℕ × ℕ))
    (f g : 𝓢(Momentum,ℂ)) (H : 𝓢(ParticleConfiguration 2,ℂ))
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (hH : HasCompactSupport H)
    (ε : ℝ) (hε : 0<ε) :
    ∃ G∈wickPurePairSpan,
      ‖wickFiniteSchwartzJetBanachCLM S G-wickPurePairTranslationIntegral S f g H‖<ε := by
  apply wick_pure_pair_jet_integral_approximation volume S _
    (wick_actual_pure_pair_jet_integrable S f g H hf hg hH) _ ε hε
  exact ae_of_all _ (fun a => by
    refine ⟨H a • wickSchwartzTranslate a (wickCovariantPairTest f g),?_,?_⟩
    · apply wickPurePairSpan.smul_mem
      rw [wick_translate_actual_pair]
      exact wick_pure_pair_mem_span _ _
    · exact (wickFiniteSchwartzJetBanachCLM S).map_smul (H a) _)

theorem wick_translate_pure_pair_span (a : ParticleConfiguration 2)
    (G : 𝓢(ParticleConfiguration 2,ℂ)) (hG : G∈wickPurePairSpan) :
    wickSchwartzTranslate a G∈wickPurePairSpan := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨⟨f,g⟩,rfl⟩ := hG
    rw [wick_translate_actual_pair]
    exact wick_pure_pair_mem_span _ _
  | zero => simpa only [map_zero] using wickPurePairSpan.zero_mem
  | add G K _ _ hG hK =>
    rw [map_add]
    exact wickPurePairSpan.add_mem hG hK
  | smul c G _ hG =>
    rw [map_smul]
    exact wickPurePairSpan.smul_mem c hG

/-- This actual integral approximation also applies to any compact test already
proved in the finite pure-pair span, including the normalized product mollifier. -/
theorem wick_pure_span_translation_integral_approximation (S : Finset (ℕ × ℕ))
    (G H : 𝓢(ParticleConfiguration 2,ℂ)) (hG : G∈wickPurePairSpan)
    (hsG : HasCompactSupport G) (hsH : HasCompactSupport H) (ε : ℝ) (hε : 0<ε) :
    ∃ K∈wickPurePairSpan,
      ‖wickFiniteSchwartzJetBanachCLM S K-
        ∫ a,H a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a G)‖<ε := by
  apply wick_pure_pair_jet_integral_approximation volume S _
    (wick_compact_weighted_translate_jet_integrable volume S G H hsG hsH) _ ε hε
  exact ae_of_all _ (fun a => by
    refine ⟨H a • wickSchwartzTranslate a G,wickPurePairSpan.smul_mem _
      (wick_translate_pure_pair_span a G hG),?_⟩
    exact (wickFiniteSchwartzJetBanachCLM S).map_smul (H a) _)

end AASCKleinGordon
