import KGPauliJordanShellDistribution

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace AASCKleinGordon
open SchwartzOperations

def commutatorFourierCorrelation (h k : 𝓢(Spacetime,ℂ)) : 𝓢(Spacetime,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (spacetimeNegationTestCLM (𝓕 h) : Spacetime → ℂ) (𝓕 k)

theorem commutatorFourierCorrelation_apply (h k : 𝓢(Spacetime,ℂ)) (q : Spacetime) :
    commutatorFourierCorrelation h k q=𝓕 h (-q)*𝓕 k q := by
  exact SchwartzMap.smulLeftCLM_apply_apply (spacetimeNegationTestCLM (𝓕 h)).hasTemperateGrowth (𝓕 k) q

def commutatorCorrelationTest (h k : 𝓢(Spacetime,ℂ)) : 𝓢(Spacetime,ℂ) :=
  𝓕⁻ (commutatorFourierCorrelation h k)

theorem fourier_commutatorCorrelationTest (h k : 𝓢(Spacetime,ℂ)) (q : Spacetime) :
    𝓕 (commutatorCorrelationTest h k) q=𝓕 h (-q)*𝓕 k q := by
  rw [commutatorCorrelationTest,FourierTransform.fourier_fourierInv_eq,commutatorFourierCorrelation_apply]

theorem positiveShell_correlation (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    positiveShellFunctionalCLM a (commutatorCorrelationTest h k)=massShellTwoPointPairing a h k := by
  change (∫ p,𝓕 (commutatorCorrelationTest h k) (shellFrequency a p) ∂wignerMeasure a)=_
  unfold massShellTwoPointPairing
  apply integral_congr_ae
  exact ae_of_all (wignerMeasure a) (fun p => by
    dsimp only
    rw [fourier_commutatorCorrelationTest,spacetimeSmearingCLM_apply,spacetimeSmearingCLM_apply,
      fourier_conjugateSchwartz_apply,star_star])

theorem negativeShell_correlation (a : Parameters) (h k : 𝓢(Spacetime,ℂ)) :
    negativeShellFunctionalCLM a (commutatorCorrelationTest h k)=massShellTwoPointPairing a k h := by
  change (∫ p,𝓕 (commutatorCorrelationTest h k) (-shellFrequency a p) ∂wignerMeasure a)=_
  unfold massShellTwoPointPairing
  apply integral_congr_ae
  exact ae_of_all (wignerMeasure a) (fun p => by
    dsimp only
    rw [fourier_commutatorCorrelationTest,neg_neg,spacetimeSmearingCLM_apply,spacetimeSmearingCLM_apply,
      fourier_conjugateSchwartz_apply,star_star,mul_comm])

theorem fieldCommutatorCoefficient_eq_spectral_distribution (a : Parameters) (s : ℝ)
    (h k : 𝓢(Spacetime,ℂ)) :
    fieldCommutatorCoefficient a s h k=(s : ℂ)^2*massShellCommutatorCLM a (commutatorCorrelationTest h k) := by
  rw [fieldCommutatorCoefficient_eq_shell_pairing]
  change _=(s : ℂ)^2*(positiveShellFunctionalCLM a (commutatorCorrelationTest h k)-
    negativeShellFunctionalCLM a (commutatorCorrelationTest h k))
  rw [positiveShell_correlation,negativeShell_correlation]

theorem spacetimeFieldCore_CCR_spectral (a : Parameters) (s : ℝ) (h k : 𝓢(Spacetime,ℂ)) :
    (spacetimeFieldCore a s h).comp (spacetimeFieldCore a s k)=
      (spacetimeFieldCore a s k).comp (spacetimeFieldCore a s h)+
        ((s : ℂ)^2*massShellCommutatorCLM a (commutatorCorrelationTest h k)) • LinearMap.id := by
  rw [spacetimeFieldCore_CCR,fieldCommutatorCoefficient_eq_spectral_distribution]

end AASCKleinGordon
