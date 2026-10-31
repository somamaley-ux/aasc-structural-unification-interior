import SchwartzCompactTranslation
import SchwartzFiniteJetBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def wickTranslationJetControl (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ)) (R T : ℝ) : ℝ :=
  ∑ i∈S,(R+T)^i.1*SchwartzMap.seminorm ℂ 0 (i.2+1) f

theorem wick_translation_jet_control_nonneg (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ))
    {R T : ℝ} (hR : 0≤R) (hT : 0≤T) : 0≤wickTranslationJetControl S f R T := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (pow_nonneg (add_nonneg hR hT) _) (apply_nonneg _ _)

theorem wick_compact_translate_finite_jet_bound (S : Finset (ℕ × ℕ)) (f : 𝓢(E,ℂ))
    {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (hradius : ∀ n x,R<‖x‖ → iteratedFDeriv ℝ n f x=0)
    {a b : E} (ha : ‖a‖≤T) (hb : ‖b‖≤T) :
    ‖wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a f)-
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate b f)‖ ≤
      wickTranslationJetControl S f R T*‖a-b‖ := by
  have he : wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a f)-
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate b f)=
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a f-wickSchwartzTranslate b f) :=
    ((wickFiniteSchwartzJetBanachCLM S).map_sub _ _).symm
  rw [he,wick_finite_jet_banach_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (wick_translation_jet_control_nonneg S f hR.le hT) (norm_nonneg _))).mpr
  intro i
  rw [wick_finite_jet_component_norm]
  apply (wick_compact_translate_seminorm_bound f hR hT hradius i.val.1 i.val.2 ha hb).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.single_le_sum (fun (j:ℕ × ℕ) _ => mul_nonneg
    (pow_nonneg (add_nonneg hR.le hT) _)
    (apply_nonneg (SchwartzMap.seminorm ℂ 0 (j.2+1)) f)) i.property

/-- Actual parameter continuity in each finite weighted-jet Banach norm. -/
theorem wick_compact_translate_finite_jet_continuous (S : Finset (ℕ × ℕ))
    (f : 𝓢(E,ℂ)) (hf : HasCompactSupport f) :
    Continuous (fun a : E => wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a f)) := by
  obtain ⟨R,hR,hradius⟩ := wick_compact_schwartz_jet_radius f hf
  apply continuous_iff_continuousAt.mpr
  intro a₀
  let T := ‖a₀‖+1
  have hT : 0≤T := by dsimp [T]; positivity
  let C := wickTranslationJetControl S f R T
  have hC : 0≤C := wick_translation_jet_control_nonneg S f hR.le hT
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 (ε/(C+1)),lt_min (by norm_num) (div_pos hε (by positivity)),?_⟩
  intro a ha
  have ha1 : ‖a-a₀‖<1 := by simpa only [dist_eq_norm] using (lt_min_iff.mp ha).1
  have haT : ‖a‖≤T := by
    have hn := norm_add_le (a-a₀) a₀
    rw [sub_add_cancel] at hn
    dsimp [T]
    linarith
  have hbT : ‖a₀‖≤T := by dsimp [T]; linarith
  have hd : ‖a-a₀‖<ε/(C+1) := by
    simpa only [dist_eq_norm] using (lt_min_iff.mp ha).2
  rw [dist_eq_norm]
  apply (wick_compact_translate_finite_jet_bound S f hR hT hradius haT hbT).trans_lt
  change C*‖a-a₀‖<ε
  have hh := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hd
  nlinarith [norm_nonneg (a-a₀)]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An actual compact scalar test weights the actual jet translation map.
Continuity and compact support prove its Bochner integrability. -/
theorem wick_compact_weighted_translate_jet_integrable (μ : Measure E)
    [IsLocallyFiniteMeasure μ] (S : Finset (ℕ × ℕ))
    (f H : 𝓢(E,ℂ)) (hf : HasCompactSupport f) (hH : HasCompactSupport H) :
    Integrable (fun a : E => H a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a f)) μ := by
  have hc : Continuous (fun a : E => H a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a f)) :=
    H.continuous.smul (wick_compact_translate_finite_jet_continuous S f hf)
  apply hc.integrable_of_hasCompactSupport
  apply hH.mono
  intro a ha
  simp only [Function.mem_support] at ha ⊢
  intro hz
  apply ha
  rw [hz,zero_smul]

end AASCKleinGordon
