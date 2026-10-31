import SchwartzPureProductMollifier
import SchwartzTranslatedJetConvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon

/-- Derivative-controlled finite-span approximation of an arbitrary compact
two-momentum test. All product kernels and normalization are constructed. -/
theorem wick_compact_pure_pair_finite_jet_approximation (S : Finset (ℕ × ℕ))
    (H : 𝓢(ParticleConfiguration 2,ℂ)) (hH : HasCompactSupport H)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ G∈wickPurePairSpan,
      ‖wickFiniteSchwartzJetBanachCLM S G-wickFiniteSchwartzJetBanachCLM S H‖<δ := by
  obtain ⟨R,hR,hradius⟩ := wick_compact_schwartz_jet_radius H hH
  let C := wickTranslationJetControl S H R 1
  have hC : 0≤C := wick_translation_jet_control_nonneg S H hR.le (by norm_num)
  let ε := min 1 (δ/(2*(C+1)))
  have hε : 0<ε := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hε1 : ε≤1 := min_le_left _ _
  have hsmall : C*ε≤δ/2 := by
    have ht := (le_div_iff₀ (show 0<2*(C+1) by positivity)).mp (min_le_right 1 (δ/(2*(C+1))))
    change ε*(2*(C+1))≤δ at ht
    nlinarith
  let P := wickPureMollifierTest ε hε
  have hP : HasCompactSupport P := wick_pure_mollifier_test_compact ε hε
  have hspan : P∈wickPurePairSpan := wick_pure_mollifier_test_span ε hε
  let I := wickTranslatedFiniteJetIntegral volume S H P
  obtain ⟨G,hG,hGI⟩ := wick_pure_span_translation_integral_approximation S P H hspan hP hH
    (δ/2) (by positivity)
  change ‖wickFiniteSchwartzJetBanachCLM S G-I‖<δ/2 at hGI
  have hcomm : I=wickTranslatedFiniteJetIntegral volume S P H :=
    wick_translated_finite_jet_integral_comm volume S H P hH hP
  have heq : I=(∫ a : ParticleConfiguration 2,wickPureMollifierWeight ε hε a •
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)) := by
    rw [hcomm]
    apply integral_congr_ae
    exact ae_of_all _ (fun a => by
      change P a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)=
        wickPureMollifierWeight ε hε a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)
      rw [show P a=(wickPureMollifierWeight ε hε a:ℂ) from wick_pure_mollifier_test_apply ε hε a]
      exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _).symm)
  have hb : ‖I-wickFiniteSchwartzJetBanachCLM S H‖≤C*ε := by
    rw [heq]
    exact wick_normalized_weight_finite_jet_error_bound volume S H hH hR hradius
      (wickPureMollifierWeight ε hε) (wick_pure_mollifier_weight_continuous ε hε)
      (wick_pure_mollifier_weight_compact ε hε) (wick_pure_mollifier_weight_nonneg ε hε)
      (wick_pure_mollifier_weight_integral ε hε) ε hε hε1
      (wick_pure_mollifier_weight_support_bound ε hε)
  refine ⟨G,hG,?_⟩
  calc
    _ ≤ ‖wickFiniteSchwartzJetBanachCLM S G-I‖+‖I-wickFiniteSchwartzJetBanachCLM S H‖ := by
      simpa only [dist_eq_norm] using
        (dist_triangle (wickFiniteSchwartzJetBanachCLM S G) I (wickFiniteSchwartzJetBanachCLM S H))
    _ < δ := by linarith [hb.trans hsmall]

/-- Localization upgrades compact approximation to every Schwartz test and
every finite family of the original weighted derivative jets. -/
theorem wick_pure_pair_finite_jet_approximation (S : Finset (ℕ × ℕ))
    (H : 𝓢(ParticleConfiguration 2,ℂ)) (δ : ℝ) (hδ : 0<δ) :
    ∃ G∈wickPurePairSpan,
      ‖wickFiniteSchwartzJetBanachCLM S G-wickFiniteSchwartzJetBanachCLM S H‖<δ := by
  have hs := ((wickFiniteSchwartzJetBanachCLM S).continuous.tendsto H).comp
    (wick_schwartz_cutoff_sequence_tendsto H)
  have he := Metric.tendsto_nhds.mp hs (δ/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let K := wickSchwartzCutoffSequence H N
  have hK : HasCompactSupport K := wick_schwartz_cutoff_sequence_compact H N
  have hd : ‖wickFiniteSchwartzJetBanachCLM S K-wickFiniteSchwartzJetBanachCLM S H‖<δ/2 := by
    simpa only [dist_eq_norm] using hN N le_rfl
  obtain ⟨G,hG,hGK⟩ := wick_compact_pure_pair_finite_jet_approximation S K hK (δ/2) (by positivity)
  refine ⟨G,hG,?_⟩
  have ht : ‖wickFiniteSchwartzJetBanachCLM S G-wickFiniteSchwartzJetBanachCLM S H‖≤
      ‖wickFiniteSchwartzJetBanachCLM S G-wickFiniteSchwartzJetBanachCLM S K‖+
      ‖wickFiniteSchwartzJetBanachCLM S K-wickFiniteSchwartzJetBanachCLM S H‖ := by
    simpa only [dist_eq_norm] using dist_triangle (wickFiniteSchwartzJetBanachCLM S G)
      (wickFiniteSchwartzJetBanachCLM S K) (wickFiniteSchwartzJetBanachCLM S H)
  exact ht.trans_lt (by linarith)

/-- Finite sums of the actual wavepacket pairs are dense in the original
Schwartz topology, using every finite family of its defining seminorms. -/
theorem wick_pure_pair_Schwartz_dense :
    Dense (wickPurePairSpan : Set 𝓢(ParticleConfiguration 2,ℂ)) := by
  intro H
  apply mem_closure_iff.mpr
  intro U hU hHU
  obtain ⟨S,r,hr,hs⟩ :=
    ((schwartz_withSeminorms ℂ (ParticleConfiguration 2) ℂ).mem_nhds_iff H U).mp
      (hU.mem_nhds hHU)
  obtain ⟨G,hG,happ⟩ := wick_pure_pair_finite_jet_approximation S H r hr
  refine ⟨G,hs ?_,hG⟩
  change S.sup (schwartzSeminormFamily ℂ (ParticleConfiguration 2) ℂ) (G-H)<r
  apply (wick_finite_jet_sup_seminorm_le S (G-H)).trans_lt
  rw [← wick_finite_jet_banach_norm S (G-H),map_sub]
  exact happ

/-- Actual finite-jet control and compact localization extend pure-pair
agreement to arbitrary continuous two-momentum distributions. -/
theorem wick_pure_pair_distribution_ext
    (A B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ)
    (hpairs : ∀ f g : 𝓢(Momentum,ℂ),A (wickCovariantPairTest f g)=B (wickCovariantPairTest f g)) :
    A=B := by
  let D := A-B
  have hspan : ∀ G∈wickPurePairSpan,D G=0 := by
    intro G hG
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨⟨f,g⟩,rfl⟩ := hG
      exact sub_eq_zero.mpr (hpairs f g)
    | zero => exact map_zero _
    | add G K _ _ hG hK => rw [map_add,hG,hK,add_zero]
    | smul c G _ hG => rw [map_smul,hG,smul_zero]
  obtain ⟨S,C,hC,hbound⟩ := wick_continuous_distribution_banach_jet_bound D
  apply wick_compact_schwartz_distribution_ext
  intro H hH
  apply sub_eq_zero.mp
  change D H=0
  by_contra hn
  have hnorm : 0<‖D H‖ := norm_pos_iff.mpr hn
  obtain ⟨G,hG,happ⟩ := wick_compact_pure_pair_finite_jet_approximation S H hH
    (‖D H‖/(C+1)) (div_pos hnorm (by positivity))
  have hzero := hspan G hG
  have hd : D (H-G)=D H := by rw [map_sub,hzero,sub_zero]
  have hb := hbound (H-G)
  rw [hd,map_sub,norm_sub_rev] at hb
  have ht := (lt_div_iff₀ (show 0<C+1 by positivity)).mp happ
  nlinarith [norm_nonneg (wickFiniteSchwartzJetBanachCLM S G-wickFiniteSchwartzJetBanachCLM S H)]

/-- SAME native-source kernel continuation uniqueness from the original actual
wavepacket square. This does not identify the full corpus physical role. -/
theorem wick_covariant_kernel_pure_pair_continuation_unique
    (a : Parameters) (s : ℝ) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ))
    (B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ)
    (hsource : ∀ f g : 𝓢(Momentum,ℂ),B (wickCovariantPairTest f g)=
      wickCovariantStrongSource a s i j h g f) :
    B=wickCovariantKernelMomentumCLM a s i j h := by
  apply wick_pure_pair_distribution_ext
  intro f g
  rw [hsource,wick_covariant_strong_kernel_square]

/-- The constructed original native kernel is the unique continuous
continuation of its actual source square on every wavepacket pair. -/
theorem wick_covariant_kernel_exists_unique_continuation
    (a : Parameters) (s : ℝ) (i j : Fin 4) (h : 𝓢(Spacetime,ℂ)) :
    ∃! B : 𝓢(ParticleConfiguration 2,ℂ) →L[ℂ] ℂ,
      ∀ f g : 𝓢(Momentum,ℂ),B (wickCovariantPairTest f g)=wickCovariantStrongSource a s i j h g f := by
  refine ⟨wickCovariantKernelMomentumCLM a s i j h,?_,?_⟩
  · exact fun f g => wick_covariant_strong_kernel_square a s i j f g h
  · exact fun B hB => wick_covariant_kernel_pure_pair_continuation_unique a s i j h B hB

end AASCKleinGordon
