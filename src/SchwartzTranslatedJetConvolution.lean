import SchwartzConvolutionJets
import SchwartzJetTranslationContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Topology
open scoped SchwartzMap Convolution ENNReal
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]

def wickTranslatedFiniteJetIntegral (S : Finset (ℕ × ℕ)) (f g : 𝓢(E,ℂ)) :
    WickFiniteJetBanach E S :=
  ∫ a,f a • wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a g) ∂μ

def wickFiniteJetComponent (S : Finset (ℕ × ℕ)) (i:S) :
    WickFiniteJetBanach E S →L[ℂ] WickJetTarget E i.val.2 where
  toFun v := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := PiLp.continuous_apply ∞ (fun j:S => WickJetTarget E j.val.2) i

def wickFiniteJetEvaluation (S : Finset (ℕ × ℕ)) (i:S) (x : E) :
    WickFiniteJetBanach E S →L[ℂ] (E [×i.val.2]→L[ℝ] ℂ) :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (wickFiniteJetComponent S i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem wick_finite_jet_evaluation_apply (S : Finset (ℕ × ℕ)) (i:S) (x : E)
    (H : 𝓢(E,ℂ)) :
    wickFiniteJetEvaluation S i x (wickFiniteSchwartzJetBanachCLM S H)=
      ‖x‖^i.val.1 • iteratedFDeriv ℝ i.val.2 H x := rfl

/-- Exact identification of every integrated weighted jet with the actual
derivative of convolution. This is the integral identity needed for density. -/
theorem wick_translated_finite_jet_integral_evaluation (S : Finset (ℕ × ℕ))
    (f g : 𝓢(E,ℂ)) (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (i:S) (x : E) :
    wickFiniteJetEvaluation S i x (wickTranslatedFiniteJetIntegral μ S f g)=
      ‖x‖^i.val.1 • iteratedFDeriv ℝ i.val.2
        ((f:E → ℂ) ⋆[ContinuousLinearMap.lsmul ℝ ℂ,μ] (g:E → ℂ)) x := by
  have hi := wick_compact_weighted_translate_jet_integrable μ S g f hg hf
  change wickFiniteJetEvaluation S i x (∫ a,f a •
    wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a g) ∂μ)=_
  rw [← (wickFiniteJetEvaluation S i x).integral_comp_comm hi,
    wick_iterated_deriv_convolution f g hg]
  rw [← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ (fun a => by
    change wickFiniteJetEvaluation S i x (f a •
      wickFiniteSchwartzJetBanachCLM S (wickSchwartzTranslate a g))=
      ‖x‖^i.val.1 • (f a • iteratedFDeriv ℝ i.val.2 g (x-a))
    rw [(wickFiniteJetEvaluation S i x).map_smul,wick_finite_jet_evaluation_apply,wick_schwartz_translate_jet]
    exact smul_comm _ _ _)

/-- The two actual Banach jet integrals agree by convolution commutativity.
No swap of nonintegrable expressions or assumed jet identity is used. -/
theorem wick_translated_finite_jet_integral_comm (S : Finset (ℕ × ℕ))
    (f g : 𝓢(E,ℂ)) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    wickTranslatedFiniteJetIntegral μ S f g=wickTranslatedFiniteJetIntegral μ S g f := by
  have hL : (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ).flip=
      ContinuousLinearMap.lsmul ℝ ℂ := by
    ext z w
    exact mul_comm _ _
  have he : ((f:E → ℂ) ⋆[ContinuousLinearMap.lsmul ℝ ℂ,μ] (g:E → ℂ))=
      ((g:E → ℂ) ⋆[ContinuousLinearMap.lsmul ℝ ℂ,μ] (f:E → ℂ)) := by
    simpa only [hL] using (convolution_flip (f:=(g:E → ℂ)) (g:=(f:E → ℂ))
      (L:=ContinuousLinearMap.lsmul ℝ ℂ) (μ:=μ))
  apply PiLp.ext
  intro i
  apply BoundedContinuousFunction.ext
  intro x
  change wickFiniteJetEvaluation S i x (wickTranslatedFiniteJetIntegral μ S f g)=
    wickFiniteJetEvaluation S i x (wickTranslatedFiniteJetIntegral μ S g f)
  rw [wick_translated_finite_jet_integral_evaluation μ S f g hf hg,
    wick_translated_finite_jet_integral_evaluation μ S g f hg hf,he]

end AASCKleinGordon
