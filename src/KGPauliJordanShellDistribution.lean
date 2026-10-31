import KGNormalOrderedFieldPairs
import KGAxisBoostSpacetimeFieldCovariance

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

def spacetimeNegationTestCLM : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Spacetime,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : Spacetime ≃L[ℝ] Spacetime)

@[simp] theorem spacetimeNegationTest_apply (h : 𝓢(Spacetime,ℂ)) (x : Spacetime) :
    spacetimeNegationTestCLM h x=h (-x) := rfl

theorem fourier_spacetimeNegationTest (h : 𝓢(Spacetime,ℂ)) (q : Spacetime) :
    𝓕 (spacetimeNegationTestCLM h) q=𝓕 h (-q) := by
  change 𝓕 (fun x : Spacetime => h (-x)) q=𝓕 (h : Spacetime → ℂ) (-q)
  exact Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (h : Spacetime → ℂ) q

def negativeFrequencySmearingCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] 𝓢(Momentum,ℂ) :=
  (shellRestrictionCLM a).comp (spacetimeNegationTestCLM.comp
    (FourierTransform.fourierCLM ℂ 𝓢(Spacetime,ℂ)))

@[simp] theorem negativeFrequencySmearing_apply (a : Parameters) (h : 𝓢(Spacetime,ℂ)) (p : Momentum) :
    negativeFrequencySmearingCLM a h p=𝓕 h (-shellFrequency a p) := rfl

def positiveShellFunctionalCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (wignerMeasure a)).comp (spacetimeSmearingCLM a)
def negativeShellFunctionalCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (wignerMeasure a)).comp (negativeFrequencySmearingCLM a)

def massShellCommutatorCLM (a : Parameters) : 𝓢(Spacetime,ℂ) →L[ℂ] ℂ :=
  positiveShellFunctionalCLM a-negativeShellFunctionalCLM a

theorem massShellCommutator_apply (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    massShellCommutatorCLM a h=
      (∫ p,𝓕 h (shellFrequency a p) ∂wignerMeasure a)-
      (∫ p,𝓕 h (-shellFrequency a p) ∂wignerMeasure a) := rfl

theorem massShellCommutator_tempered (a : Parameters) : Continuous (massShellCommutatorCLM a) :=
  (massShellCommutatorCLM a).continuous

theorem massShellCommutator_odd (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    massShellCommutatorCLM a (spacetimeNegationTestCLM h)= -massShellCommutatorCLM a h := by
  rw [massShellCommutator_apply,massShellCommutator_apply]
  simp only [fourier_spacetimeNegationTest,neg_neg]
  ring

theorem negativeFrequencySmearing_kleinGordon_zero (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    negativeFrequencySmearingCLM a (kleinGordonSchwartzCLM a h)=0 := by
  ext p
  rw [negativeFrequencySmearing_apply,fourier_kleinGordonSchwartz_apply,
    kleinGordonSymbol_neg,kleinGordonSymbol_on_shell]
  simp

theorem massShellCommutator_kleinGordon (a : Parameters) (h : 𝓢(Spacetime,ℂ)) :
    massShellCommutatorCLM a (kleinGordonSchwartzCLM a h)=0 := by
  change (SchwartzMap.integralCLM ℂ (wignerMeasure a)) (spacetimeSmearingCLM a (kleinGordonSchwartzCLM a h))-
    (SchwartzMap.integralCLM ℂ (wignerMeasure a)) (negativeFrequencySmearingCLM a (kleinGordonSchwartzCLM a h))=0
  rw [spacetimeSmearing_kleinGordon_zero,negativeFrequencySmearing_kleinGordon_zero,map_zero,sub_self]

end AASCKleinGordon
