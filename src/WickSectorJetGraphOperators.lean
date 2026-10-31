import WickSchwartzJetGraph
import WickCoreSeminormSums

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap NNReal DirectSum BoundedContinuousFunction
namespace AASCKleinGordon

structure WickJetGraphIndex where
  jets : ℕ → Finset (ℕ × ℕ)
  weights : ℕ → NNReal

abbrev WickFiniteJetSpace (n : ℕ) (J : Finset (ℕ × ℕ)) :=
  ∀ j : J,WickJetTarget (ParticleConfiguration n) j.val.2

-- Pin the pointwise module instance explicitly: unconstrained Pi module
-- search otherwise explores irrelevant scalar towers before Pi.module.
instance wickFiniteJetModule (n : ℕ) (J : Finset (ℕ × ℕ)) :
    Module ℂ (WickFiniteJetSpace n J) :=
  Pi.module J (fun j => WickJetTarget (ParticleConfiguration n) j.val.2) ℂ

instance wickFiniteJetNormedSpace (n : ℕ) (J : Finset (ℕ × ℕ)) :
    NormedSpace ℂ (WickFiniteJetSpace n J) := Pi.normedSpace

instance wickFiniteJetSMulZeroClass (n : ℕ) (J : Finset (ℕ × ℕ)) :
    SMulZeroClass ℂ (WickFiniteJetSpace n J) where
  smul_zero c := by
    funext j
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro y
    change c*(0:ℂ)=0
    exact mul_zero c

instance wickFiniteJetDistribSMul (n : ℕ) (J : Finset (ℕ × ℕ)) :
    DistribSMul ℂ (WickFiniteJetSpace n J) where
  smul_zero c := wickFiniteJetSMulZeroClass n J |>.smul_zero c
  smul_add c f g := by
    funext j
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro y
    change c*(f j x y+g j x y)=c*f j x y+c*g j x y
    exact mul_add _ _ _

instance wickFiniteJetNormSMulClass (n : ℕ) (J : Finset (ℕ × ℕ)) :
    NormSMulClass ℂ (WickFiniteJetSpace n J) := NormedSpace.toNormSMulClass (𝕜:=ℂ) (E:=WickFiniteJetSpace n J)

abbrev WickJetGraphSpace (σ : WickJetGraphIndex) :=
  lp (fun n => WickFiniteJetSpace n (σ.jets n)) 1

def wickFiniteJetCLM (n : ℕ) (J : Finset (ℕ × ℕ)) :
    𝓢(ParticleConfiguration n,ℂ) →L[ℂ] WickFiniteJetSpace n J :=
  ContinuousLinearMap.pi (fun j => wickSchwartzJetCLM j.val.1 j.val.2)

lemma wick_finite_jet_norm (n : ℕ) (J : Finset (ℕ × ℕ)) (f : 𝓢(ParticleConfiguration n,ℂ)) :
    ‖wickFiniteJetCLM n J f‖=J.sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) f := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (apply_nonneg _ _)).mpr
    intro j
    change ‖wickSchwartzJetCLM j.val.1 j.val.2 f‖≤_
    rw [wick_schwartz_jet_CLM_apply,wick_schwartz_jet_norm]
    exact Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) (x:=f) j.property
  · apply Seminorm.finset_sup_apply_le (norm_nonneg _)
    intro j hj
    have h := norm_le_pi_norm (wickFiniteJetCLM n J f) (⟨j,hj⟩ : J)
    simpa only [wickFiniteJetCLM,ContinuousLinearMap.pi_apply,
      wick_schwartz_jet_CLM_apply,wick_schwartz_jet_norm] using h

def wickBosonicSchwartzSubtypeCLM (n : ℕ) :
    bosonicSchwartz n →L[ℂ] 𝓢(ParticleConfiguration n,ℂ) :=
  ⟨(bosonicSchwartz n).subtype,continuous_subtype_val⟩

def wickJetGraphSectorCLM (σ : WickJetGraphIndex) (n : ℕ) :
    bosonicSchwartz n →L[ℂ] WickJetGraphSpace σ :=
  (((σ.weights n : ℝ):ℂ)) • (lp.singleContinuousLinearMap ℂ
    (fun m => WickFiniteJetSpace m (σ.jets m)) 1 n).comp
      ((wickFiniteJetCLM n (σ.jets n)).comp (wickBosonicSchwartzSubtypeCLM n))

/-- A genuine Banach-valued graph operator on the ORIGINAL finite-particle
Schwartz domain, fixed from jets/weights before any stress or source response. -/
def wickJetGraphLM (σ : WickJetGraphIndex) : FiniteParticleCore →ₗ[ℂ] WickJetGraphSpace σ :=
  DirectSum.toModule ℂ ℕ (WickJetGraphSpace σ) (fun n => (wickJetGraphSectorCLM σ n).toLinearMap)

lemma wick_jet_graph_LM_lof (σ : WickJetGraphIndex) (n : ℕ) (f : bosonicSchwartz n) :
    wickJetGraphLM σ (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n f)=wickJetGraphSectorCLM σ n f :=
  by
  simpa only [wickJetGraphLM] using (DirectSum.toModule_lof ℂ (φ:=fun m => (wickJetGraphSectorCLM σ m).toLinearMap) n f)

lemma wick_jet_graph_LM_continuous (σ : WickJetGraphIndex) : Continuous (wickJetGraphLM σ) := by
  apply (core_normed_linearMap_continuous_iff (wickJetGraphLM σ)).mpr
  intro n
  have he : (wickJetGraphLM σ).comp (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) n)=
      (wickJetGraphSectorCLM σ n).toLinearMap := by
    apply LinearMap.ext
    intro f
    exact wick_jet_graph_LM_lof σ n f
  rw [he]
  exact (wickJetGraphSectorCLM σ n).continuous

def wickJetGraphCLM (σ : WickJetGraphIndex) : FiniteParticleCore →L[ℂ] WickJetGraphSpace σ :=
  ⟨wickJetGraphLM σ,wick_jet_graph_LM_continuous σ⟩

lemma wick_jet_graph_coordinate (σ : WickJetGraphIndex) (u : FiniteParticleCore) (n : ℕ) :
    wickJetGraphCLM σ u n=(((σ.weights n : ℝ):ℂ)) • wickFiniteJetCLM n (σ.jets n) (u n).val := by
  induction u using DirectSum.induction_on with
  | zero =>
    change (wickJetGraphCLM σ 0) n=_
    rw [map_zero,lp.coeFn_zero]
    change (0 : WickFiniteJetSpace n (σ.jets n))= _ • wickFiniteJetCLM n (σ.jets n) 0
    rw [map_zero,smul_zero]
  | of m f =>
    change wickJetGraphLM σ (DirectSum.lof ℂ ℕ (fun n => bosonicSchwartz n) m f) n=_
    rw [wick_jet_graph_LM_lof]
    simp only [wickJetGraphSectorCLM,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      lp.singleContinuousLinearMap_apply,lp.coeFn_smul,lp.coeFn_single,Pi.smul_apply]
    by_cases hm : m=n
    · subst m
      rw [DirectSum.of_eq_same,Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne (Ne.symm hm),DirectSum.of_eq_of_ne _ _ _ (Ne.symm hm)]
      simp
  | add u v hu hv =>
    change (wickJetGraphCLM σ (u+v)) n=_
    rw [map_add,lp.coeFn_add,Pi.add_apply,hu,hv]
    change _=(((σ.weights n : ℝ):ℂ)) •
      wickFiniteJetCLM n (σ.jets n) ((u n).val+(v n).val)
    rw [map_add]
    exact (smul_add (((σ.weights n : ℝ):ℂ))
      (wickFiniteJetCLM n (σ.jets n) (u n).val)
      (wickFiniteJetCLM n (σ.jets n) (v n).val)).symm

lemma wick_jet_graph_norm (σ : WickJetGraphIndex) (u : FiniteParticleCore) :
    ‖wickJetGraphCLM σ u‖=∑' n,(σ.weights n : ℝ)*
      (σ.jets n).sup (schwartzSeminormFamily ℂ (ParticleConfiguration n) ℂ) (u n).val := by
  rw [lp.norm_eq_tsum_rpow (show 0<(1:ENNReal).toReal by norm_num)]
  norm_num only [ENNReal.toReal_one,one_div,Real.rpow_one]
  apply tsum_congr
  intro n
  rw [wick_jet_graph_coordinate,norm_smul,wick_finite_jet_norm]
  simp [Complex.norm_real,abs_of_nonneg (σ.weights n).coe_nonneg]

end AASCKleinGordon
