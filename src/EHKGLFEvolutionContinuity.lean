import EHKGCurvedPhaseDecomposition

/-! LF continuous dependence of the actual compact-data evolution. The
smooth compact-open topology is defined explicitly by all actual Frechet
derivatives on all compact sets. Continuity of the chosen global smooth
extensions implies the required continuity on the protected PDE domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Filter MeasureTheory TopologicalSpace AASCSemanticExhaustion
open scoped SchwartzMap FourierTransform Topology
namespace AASCKleinGordon.CurvedKG

def curvedPhaseJetCLM (a : Parameters) (sign : ℝ) (c : ℂ)
    (K : Compacts CoordinatePoint) (n : ℕ) :
    𝓢(KGSpatialSpace, ℂ) →L[ℝ]
      C(K, ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinatePoint) ℝ) :=
  { weightedPhaseJetLinearMap (homogeneousPhaseFrequency (auxiliaryKGParameters a) sign)
      (homogeneous_phase_frequency_temperate _ _) coordinateSpacetimeCLM (realCoefficientCLM c)
      (curvedCosineWeight a) (curved_cosine_weight_smooth a) K n with
    cont := weighted_phase_jet_continuous _ (homogeneous_phase_frequency_temperate _ _) _ _ _
      (curved_cosine_weight_smooth a) K n }

theorem compact_curved_jet_four_phase (a : Parameters) (U : Opens KGSpatialSpace)
    (f h : TestFunction U ℝ (⊤ : ℕ∞)) (K : Compacts CoordinatePoint) (n : ℕ) :
    compactRealJet (compactCurvedField a U f h) (compact_curved_field_smooth a U f h) K n =
      ((curvedPhaseJetCLM a 1 (1 / 2) K n (compactFourierDataCLM U f) +
        curvedPhaseJetCLM a (-1) (1 / 2) K n (compactFourierDataCLM U f)) +
        curvedPhaseJetCLM a 1 ((2 * Complex.I)⁻¹) K n (compactSineFourierDataCLM a U h)) +
        curvedPhaseJetCLM a (-1) (-((2 * Complex.I)⁻¹)) K n (compactSineFourierDataCLM a U h) := by
  have r1 : ContDiff ℝ n (curvedWeightedPhase a 1 (1 / 2) (compactFourierDataCLM U f)) :=
    (curved_weighted_phase_smooth _ _ _ _).of_le (by exact_mod_cast le_top)
  have r2 : ContDiff ℝ n (curvedWeightedPhase a (-1) (1 / 2) (compactFourierDataCLM U f)) :=
    (curved_weighted_phase_smooth _ _ _ _).of_le (by exact_mod_cast le_top)
  have r3 : ContDiff ℝ n (curvedWeightedPhase a 1 ((2 * Complex.I)⁻¹) (compactSineFourierDataCLM a U h)) :=
    (curved_weighted_phase_smooth _ _ _ _).of_le (by exact_mod_cast le_top)
  have r4 : ContDiff ℝ n (curvedWeightedPhase a (-1) (-((2 * Complex.I)⁻¹)) (compactSineFourierDataCLM a U h)) :=
    (curved_weighted_phase_smooth _ _ _ _).of_le (by exact_mod_cast le_top)
  apply ContinuousMap.ext
  intro p
  change iteratedFDeriv ℝ n (compactCurvedField a U f h) p = _
  rw [compact_curved_four_phase]
  have jetAdd (F G : CoordinatePoint → ℝ) (rF : ContDiff ℝ n F) (rG : ContDiff ℝ n G) :
      iteratedFDeriv ℝ n (F + G) p = iteratedFDeriv ℝ n F p + iteratedFDeriv ℝ n G p :=
    iteratedFDeriv_add_apply rF.contDiffAt rG.contDiffAt
  let F1 := curvedWeightedPhase a 1 (1 / 2) (compactFourierDataCLM U f)
  let F2 := curvedWeightedPhase a (-1) (1 / 2) (compactFourierDataCLM U f)
  let F3 := curvedWeightedPhase a 1 ((2 * Complex.I)⁻¹) (compactSineFourierDataCLM a U h)
  let F4 := curvedWeightedPhase a (-1) (-((2 * Complex.I)⁻¹)) (compactSineFourierDataCLM a U h)
  change iteratedFDeriv ℝ n (((F1 + F2) + F3) + F4) p = _
  rw [jetAdd ((F1 + F2) + F3) F4 ((r1.add r2).add r3) r4,
    jetAdd (F1 + F2) F3 (r1.add r2) r3, jetAdd F1 F2 r1 r2]
  rfl

theorem compact_curved_all_jets_lf_continuous (a : Parameters) (U : Opens KGSpatialSpace)
    (K : Compacts CoordinatePoint) (n : ℕ) :
    Continuous (fun data : TestFunction U ℝ (⊤ : ℕ∞) × TestFunction U ℝ (⊤ : ℕ∞) =>
      compactRealJet (compactCurvedField a U data.1 data.2)
        (compact_curved_field_smooth a U data.1 data.2) K n) := by
  have fourierFirst : Continuous (fun data : TestFunction U ℝ (⊤ : ℕ∞) × TestFunction U ℝ (⊤ : ℕ∞) =>
      compactFourierDataCLM U data.1) := (compactFourierDataCLM U).continuous.comp continuous_fst
  have sineSecond : Continuous (fun data : TestFunction U ℝ (⊤ : ℕ∞) × TestFunction U ℝ (⊤ : ℕ∞) =>
      compactSineFourierDataCLM a U data.2) := (compactSineFourierDataCLM a U).continuous.comp continuous_snd
  have h1 := (curvedPhaseJetCLM a 1 (1 / 2) K n).continuous.comp fourierFirst
  have h2 := (curvedPhaseJetCLM a (-1) (1 / 2) K n).continuous.comp
    fourierFirst
  have h3 := (curvedPhaseJetCLM a 1 ((2 * Complex.I)⁻¹) K n).continuous.comp
    sineSecond
  have h4 := (curvedPhaseJetCLM a (-1) (-((2 * Complex.I)⁻¹)) K n).continuous.comp
    sineSecond
  convert ((h1.add h2).add h3).add h4 using 1
  funext data
  exact compact_curved_jet_four_phase a U data.1 data.2 K n

def SmoothRealGlobalField := {F : CoordinatePoint → ℝ // ContDiff ℝ (⊤ : ℕ∞) F}

def smoothRealGlobalJetEmbedding (F : SmoothRealGlobalField) :
    (n : ℕ) → (K : Compacts CoordinatePoint) →
      C(K, ContinuousMultilinearMap ℝ (fun _ : Fin n => CoordinatePoint) ℝ) :=
  fun n K => compactRealJet F.val F.property K n

instance smoothRealGlobalFieldTopology : TopologicalSpace SmoothRealGlobalField :=
  TopologicalSpace.induced smoothRealGlobalJetEmbedding inferInstance

def compactCurvedSmoothEvolution (a : Parameters) (U : Opens KGSpatialSpace)
    (data : TestFunction U ℝ (⊤ : ℕ∞) × TestFunction U ℝ (⊤ : ℕ∞)) : SmoothRealGlobalField :=
  ⟨compactCurvedField a U data.1 data.2, compact_curved_field_smooth a U data.1 data.2⟩

theorem compact_curved_evolution_lf_to_smooth_compact_open (a : Parameters)
    (U : Opens KGSpatialSpace) : Continuous (compactCurvedSmoothEvolution a U) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  apply continuous_pi
  intro K
  exact compact_curved_all_jets_lf_continuous a U K n

end AASCKleinGordon.CurvedKG
