import SchwartzFiniteJetLocalization
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 200000
open scoped SchwartzMap ENNReal
namespace AASCKleinGordon

/-- The same finite weighted jets, packaged with the canonical sup norm so
Bochner integration uses a single coherent norm/topology instance. -/
def WickFiniteJetBanach (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset (ℕ × ℕ)) := PiLp ∞ (fun i:S => WickJetTarget E i.val.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An ordinary type definition fences off competing generic WithLp instances.
All structures below come from the SAME inherited infinity-norm product. -/
instance wickFiniteJetBanachNormedGroup (S : Finset (ℕ × ℕ)) :
    NormedAddCommGroup (WickFiniteJetBanach E S) :=
  inferInstanceAs (NormedAddCommGroup (PiLp ∞ (fun i:S => WickJetTarget E i.val.2)))

instance wickFiniteJetBanachComplexSpace (S : Finset (ℕ × ℕ)) :
    NormedSpace ℂ (WickFiniteJetBanach E S) :=
  inferInstanceAs (NormedSpace ℂ (PiLp ∞ (fun i:S => WickJetTarget E i.val.2)))

instance wickFiniteJetBanachRealSpace (S : Finset (ℕ × ℕ)) :
    NormedSpace ℝ (WickFiniteJetBanach E S) :=
  inferInstanceAs (NormedSpace ℝ (PiLp ∞ (fun i:S => WickJetTarget E i.val.2)))

instance wickFiniteJetBanachComplete (S : Finset (ℕ × ℕ)) :
    CompleteSpace (WickFiniteJetBanach E S) :=
  inferInstanceAs (CompleteSpace (PiLp ∞ (fun i:S => WickJetTarget E i.val.2)))

instance wickFiniteJetBanachCoeFun (S : Finset (ℕ × ℕ)) :
    CoeFun (WickFiniteJetBanach E S) (fun _ => (i:S) → WickJetTarget E i.val.2) where
  coe v := WithLp.ofLp v

def wickFiniteSchwartzJetBanachCLM (S : Finset (ℕ × ℕ)) :
    𝓢(E,ℂ) →L[ℂ] WickFiniteJetBanach E S where
  toFun f := WithLp.toLp ∞ (wickFiniteSchwartzJetCLM S f)
  map_add' f g := by
    apply PiLp.ext
    intro i
    exact congrFun ((wickFiniteSchwartzJetCLM S).map_add f g) i
  map_smul' c f := by
    apply PiLp.ext
    intro i
    exact congrFun ((wickFiniteSchwartzJetCLM S).map_smul c f) i
  cont := (PiLp.continuous_toLp ∞ _).comp (wickFiniteSchwartzJetCLM S).continuous

theorem wick_finite_jet_banach_complete (S : Finset (ℕ × ℕ)) :
    CompleteSpace (WickFiniteJetBanach E S) := inferInstance

theorem wick_finite_jet_banach_apply (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ)) (i:S) :
    wickFiniteSchwartzJetBanachCLM S f i=wickSchwartzJetCLM i.val.1 i.val.2 f := rfl

/-- Exact equality with the inherited finite-jet norm. No seminorm is dropped. -/
theorem wick_finite_jet_banach_norm (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ)) :
    ‖wickFiniteSchwartzJetBanachCLM S f‖=‖wickFiniteSchwartzJetCLM S f‖ := by
  change ‖WithLp.toLp ∞ (wickFiniteSchwartzJetCLM S f)‖=‖wickFiniteSchwartzJetCLM S f‖
  exact PiLp.norm_toLp (β:=fun i:S => WickJetTarget E i.val.2) (wickFiniteSchwartzJetCLM S f)

theorem wick_finite_jet_banach_component_norm (S : Finset (ℕ × ℕ))
    (f : 𝓢(E,ℂ)) (i:S) :
    ‖wickFiniteSchwartzJetBanachCLM S f i‖=SchwartzMap.seminorm ℂ i.val.1 i.val.2 f :=
  wick_schwartz_jet_norm _ _ f

theorem wick_continuous_distribution_banach_jet_bound (A : 𝓢(E,ℂ) →L[ℂ] ℂ) :
    ∃ S : Finset (ℕ × ℕ),∃ C : ℝ,0≤C ∧
      ∀ f : 𝓢(E,ℂ),‖A f‖≤C*‖wickFiniteSchwartzJetBanachCLM S f‖ := by
  obtain ⟨S,C,hC,hb⟩ := wick_continuous_distribution_finite_jet_bound A
  exact ⟨S,C,hC,fun f => by rw [wick_finite_jet_banach_norm];exact hb f⟩

end AASCKleinGordon
