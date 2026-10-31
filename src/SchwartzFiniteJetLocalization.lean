import SchwartzCompactTestSeparation
import WickSchwartzJetGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine Banach-valued finite family of weighted derivative jets.
The Schwartz topology is retained; this is not declared an equivalent single norm. -/
def wickFiniteSchwartzJetCLM (S : Finset (ℕ × ℕ)) :
    𝓢(E,ℂ) →L[ℂ] ((i : S) → WickJetTarget E i.val.2) :=
  ContinuousLinearMap.pi (fun i : S => wickSchwartzJetCLM i.val.1 i.val.2)

theorem wick_finite_schwartz_jet_complete_space (S : Finset (ℕ × ℕ)) :
    CompleteSpace ((i : S) → WickJetTarget E i.val.2) := inferInstance

theorem wick_finite_jet_component_norm (S : Finset (ℕ × ℕ)) (i : S) (f : 𝓢(E,ℂ)) :
    ‖wickFiniteSchwartzJetCLM S f i‖=SchwartzMap.seminorm ℂ i.val.1 i.val.2 f :=
  wick_schwartz_jet_norm _ _ f

theorem wick_finite_jet_sup_seminorm_le (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ)) :
    S.sup (schwartzSeminormFamily ℂ E ℂ) f≤‖wickFiniteSchwartzJetCLM S f‖ := by
  apply Seminorm.finset_sup_apply_le (norm_nonneg _)
  intro i hi
  change SchwartzMap.seminorm ℂ i.1 i.2 f≤_
  rw [← wick_finite_jet_component_norm S ⟨i,hi⟩ f]
  exact norm_le_pi_norm (wickFiniteSchwartzJetCLM S f) (⟨i,hi⟩ : S)

/-- Every actual continuous distribution is controlled by finitely many
actual weighted jets. No tensor-density or approximation conclusion is assumed. -/
theorem wick_continuous_distribution_finite_jet_bound (A : 𝓢(E,ℂ) →L[ℂ] ℂ) :
    ∃ S : Finset (ℕ × ℕ),∃ C : ℝ,0≤C ∧
      ∀ f : 𝓢(E,ℂ),‖A f‖≤C*‖wickFiniteSchwartzJetCLM S f‖ := by
  let p := (normSeminorm ℂ ℂ).comp A.toLinearMap
  have hp : Continuous p := A.continuous.norm
  obtain ⟨S,C,_hC,hb⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) p hp
  refine ⟨S,(C:ℝ),C.coe_nonneg,?_⟩
  intro f
  exact (hb f).trans (mul_le_mul_of_nonneg_left (wick_finite_jet_sup_seminorm_le S f) C.coe_nonneg)

variable [FiniteDimensional ℝ E]

theorem wick_schwartz_cutoff_finite_jets_tendsto (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ)) :
    Tendsto (fun N => wickFiniteSchwartzJetCLM S (wickSchwartzCutoffSequence f N))
      atTop (𝓝 (wickFiniteSchwartzJetCLM S f)) :=
  ((wickFiniteSchwartzJetCLM S).continuous.tendsto f).comp
    (wick_schwartz_cutoff_sequence_tendsto f)

theorem wick_compact_schwartz_finite_jet_approximation (S : Finset (ℕ × ℕ))
    (f : 𝓢(E,ℂ)) (ε : ℝ) (hε : 0<ε) :
    ∃ g : 𝓢(E,ℂ),HasCompactSupport g ∧
      ‖wickFiniteSchwartzJetCLM S g-wickFiniteSchwartzJetCLM S f‖<ε := by
  have hs := (Metric.tendsto_nhds.mp (wick_schwartz_cutoff_finite_jets_tendsto S f)) ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp hs
  refine ⟨wickSchwartzCutoffSequence f N,wick_schwartz_cutoff_sequence_compact f N,?_⟩
  have hd : dist (wickFiniteSchwartzJetCLM S (wickSchwartzCutoffSequence f N))
      (wickFiniteSchwartzJetCLM S f)=
      ‖wickFiniteSchwartzJetCLM S (wickSchwartzCutoffSequence f N)-wickFiniteSchwartzJetCLM S f‖ :=
    dist_eq_norm (wickFiniteSchwartzJetCLM S (wickSchwartzCutoffSequence f N))
      (wickFiniteSchwartzJetCLM S f)
  rw [← hd]
  exact hN N le_rfl

end AASCKleinGordon
