import SchwartzJetTranslationContinuity
import Mathlib.Analysis.Calculus.BumpFunction.Normed

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap
namespace AASCKleinGordon


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def wickJetMollifierBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0<ε) : ContDiffBump (0:E) :=
  ⟨ε/2,ε,by positivity,by linarith⟩

variable (μ : Measure E) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]

/-- A genuine integral in the finite-jet Banach space, not in Schwartz space. -/
def wickMollifiedFiniteJet (S : Finset (ℕ × ℕ)) (H : 𝓢(E,ℂ))
    (ε : ℝ) (hε : 0<ε) :=
  ∫ a : E,(wickJetMollifierBump E ε hε).normed μ a •
    wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H) ∂μ

theorem wick_mollified_finite_jet_integrable (S : Finset (ℕ × ℕ))
    (H : 𝓢(E,ℂ)) (hH : HasCompactSupport H) (ε : ℝ) (hε : 0<ε) :
    Integrable (fun a : E => (wickJetMollifierBump E ε hε).normed μ a •
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)) μ := by
  have hc : Continuous (fun a : E => (wickJetMollifierBump E ε hε).normed μ a •
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)) :=
    (wickJetMollifierBump E ε hε).continuous_normed.smul
    (wick_compact_translate_finite_jet_continuous S H hH)
  apply hc.integrable_of_hasCompactSupport
  apply ((wickJetMollifierBump E ε hε).hasCompactSupport_normed (μ:=μ)).mono
  intro a ha
  simp only [Function.mem_support] at ha ⊢
  intro hz
  apply ha
  rw [hz,zero_smul]

/-- An explicit uniform weighted-derivative error bound for normalized smoothing.
The original compact H remains entangled; pure-pair span membership is separate. -/
theorem wick_mollified_finite_jet_error_bound (S : Finset (ℕ × ℕ))
    (H : 𝓢(E,ℂ)) (hH : HasCompactSupport H)
    {R : ℝ} (hR : 0<R)
    (hradius : ∀ n x,R<‖x‖ → iteratedFDeriv ℝ n H x=0)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ‖wickMollifiedFiniteJet μ S H ε hε-wickFiniteSchwartzJetBanachCLM S H‖ ≤
      wickTranslationJetControl S H R 1*ε := by
  let ρ := (wickJetMollifierBump E ε hε).normed μ
  let Φ := fun a : E => wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)
  let C := wickTranslationJetControl S H R 1
  have hC : 0≤C := wick_translation_jet_control_nonneg S H hR.le (by norm_num)
  have hρ : Integrable ρ μ := (wickJetMollifierBump E ε hε).integrable_normed
  have hΦ := wick_mollified_finite_jet_integrable μ S H hH ε hε
  have hconst : Integrable (fun a : E => ρ a • wickFiniteSchwartzJetBanachCLM S H) μ :=
    hρ.smul_const _
  have heq : (∫ a,ρ a • wickFiniteSchwartzJetBanachCLM S H ∂μ)=wickFiniteSchwartzJetBanachCLM S H :=
    (wickJetMollifierBump E ε hε).integral_normed_smul μ _
  have hbound : ∀ a : E,‖ρ a • Φ a-ρ a • wickFiniteSchwartzJetBanachCLM S H‖≤ρ a*(C*ε) := by
    intro a
    by_cases ha : ρ a=0
    · simp only [ha,zero_smul,sub_self,norm_zero,zero_mul,le_refl]
    have haε : ‖a‖<ε := by
      have hm : a∈Function.support ((wickJetMollifierBump E ε hε).normed μ) := ha
      rw [(wickJetMollifierBump E ε hε).support_normed_eq] at hm
      simpa only [Metric.mem_ball,dist_zero_right,wickJetMollifierBump] using hm
    have hd := wick_compact_translate_finite_jet_bound S H hR (show (0:ℝ)≤1 by norm_num)
      hradius (a:=a) (b:=0) (haε.le.trans hε1) (by simp)
    rw [wick_schwartz_translate_zero,sub_zero] at hd
    have hρa : 0≤ρ a := (wickJetMollifierBump E ε hε).nonneg_normed a
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hρa]
    exact mul_le_mul_of_nonneg_left (hd.trans
      (mul_le_mul_of_nonneg_left haε.le hC)) hρa
  change ‖(∫ a,ρ a • Φ a ∂μ)-wickFiniteSchwartzJetBanachCLM S H‖≤C*ε
  rw [← heq,← integral_sub hΦ hconst]
  calc
    _ ≤ ∫ a,‖ρ a • Φ a-ρ a • wickFiniteSchwartzJetBanachCLM S H‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a,ρ a*(C*ε) ∂μ := integral_mono_ae (hΦ.sub hconst).norm
      (hρ.mul_const _) (ae_of_all _ hbound)
    _ = C*ε := by
      rw [integral_mul_const,(wickJetMollifierBump E ε hε).integral_normed,one_mul]

omit [μ.IsOpenPosMeasure]

/-- The same quantitative estimate for any actual nonnegative normalized compact
weight. The concrete pure product mollifier will discharge every weight premise. -/
theorem wick_normalized_weight_finite_jet_error_bound (S : Finset (ℕ × ℕ))
    (H : 𝓢(E,ℂ)) (hH : HasCompactSupport H)
    {R : ℝ} (hR : 0<R)
    (hradius : ∀ n x,R<‖x‖ → iteratedFDeriv ℝ n H x=0)
    (ρ : E → ℝ) (hcρ : Continuous ρ) (hsρ : HasCompactSupport ρ)
    (hnρ : ∀ a,0≤ρ a) (hiρ : (∫ a,ρ a ∂μ)=1)
    (ε : ℝ) (_hε : 0<ε) (hε1 : ε≤1)
    (hsupport : ∀ a,ρ a≠0 → ‖a‖≤ε) :
    ‖(∫ a,ρ a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H) ∂μ)-
      wickFiniteSchwartzJetBanachCLM S H‖ ≤ wickTranslationJetControl S H R 1*ε := by
  let Φ := fun a : E => wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a H)
  let C := wickTranslationJetControl S H R 1
  have hC : 0≤C := wick_translation_jet_control_nonneg S H hR.le (by norm_num)
  have hρ : Integrable ρ μ := hcρ.integrable_of_hasCompactSupport hsρ
  have hΦ : Integrable (fun a => ρ a • Φ a) μ := by
    apply (hcρ.smul (wick_compact_translate_finite_jet_continuous S H hH)).integrable_of_hasCompactSupport
    apply hsρ.mono
    intro a ha
    simp only [Function.mem_support] at ha ⊢
    intro hz
    exact ha (by rw [hz,zero_smul])
  have hconst : Integrable (fun a : E => ρ a • wickFiniteSchwartzJetBanachCLM S H) μ := hρ.smul_const _
  have heq : (∫ a,ρ a • wickFiniteSchwartzJetBanachCLM S H ∂μ)=wickFiniteSchwartzJetBanachCLM S H := by
    rw [integral_smul_const,hiρ,one_smul]
  have hbound : ∀ a : E,‖ρ a • Φ a-ρ a • wickFiniteSchwartzJetBanachCLM S H‖≤ρ a*(C*ε) := by
    intro a
    by_cases ha : ρ a=0
    · simp only [ha,zero_smul,sub_self,norm_zero,zero_mul,le_refl]
    have haε := hsupport a ha
    have hd := wick_compact_translate_finite_jet_bound S H hR (show (0:ℝ)≤1 by norm_num)
      hradius (a:=a) (b:=0) (haε.trans hε1) (by simp)
    rw [wick_schwartz_translate_zero,sub_zero] at hd
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (hnρ a)]
    exact mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left haε hC)) (hnρ a)
  change ‖(∫ a,ρ a • Φ a ∂μ)-wickFiniteSchwartzJetBanachCLM S H‖≤C*ε
  rw [← heq,← integral_sub hΦ hconst]
  calc
    _ ≤ ∫ a,‖ρ a • Φ a-ρ a • wickFiniteSchwartzJetBanachCLM S H‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a,ρ a*(C*ε) ∂μ := integral_mono_ae (hΦ.sub hconst).norm (hρ.mul_const _) (ae_of_all _ hbound)
    _ = C*ε := by rw [integral_mul_const,hiρ,one_mul]

end AASCKleinGordon
