import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open MeasureTheory Filter Topology
open scoped SchwartzMap Convolution
namespace AASCKleinGordon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Every derivative of the actual compact Schwartz convolution is its
corresponding Bochner jet integral. No distributional equality is assumed. -/
theorem wick_iterated_deriv_convolution (f g : 𝓢(E,ℂ))
    (hg : HasCompactSupport g) (n : ℕ) (x : E) :
    iteratedFDeriv ℝ n ((f:E → ℂ) ⋆[ContinuousLinearMap.lsmul ℝ ℂ,μ] (g:E → ℂ)) x=
      ∫ a,f a • iteratedFDeriv ℝ n g (x-a) ∂μ := by
  induction n generalizing x with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ E ℂ).symm.toLinearIsometry
    rw [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    change L (∫ a,f a*g (x-a) ∂μ)=∫ a,f a • L (g (x-a)) ∂μ
    rw [← L.integral_comp_comm]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => rfl)
  | succ n ih =>
    letI : NormedAddCommGroup (E [×n]→L[ℝ] ℂ) := ContinuousMultilinearMap.normedAddCommGroup'
    letI : NormedSpace ℝ (E [×n]→L[ℝ] ℂ) := ContinuousMultilinearMap.normedSpace'
    letI : NormedSpace ℂ (E [×n]→L[ℝ] ℂ) := ContinuousMultilinearMap.normedSpace'
    letI : NormedAddCommGroup (E →L[ℝ] (E [×n]→L[ℝ] ℂ)) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (E →L[ℝ] (E [×n]→L[ℝ] ℂ)) := ContinuousLinearMap.toNormedSpace
    letI : NormedSpace ℂ (E →L[ℝ] (E [×n]→L[ℝ] ℂ)) := ContinuousLinearMap.toNormedSpace
    let B : ℂ →L[ℝ] (E [×n]→L[ℝ] ℂ) →L[ℝ] (E [×n]→L[ℝ] ℂ) :=
      ContinuousLinearMap.lsmul ℝ ℂ
    have he : iteratedFDeriv ℝ n ((f:E → ℂ) ⋆[ContinuousLinearMap.lsmul ℝ ℂ,μ] (g:E → ℂ))=
        ((f:E → ℂ) ⋆[B,μ] iteratedFDeriv ℝ n g) := funext ih
    have hn : ContDiff ℝ 1 (iteratedFDeriv ℝ n g) :=
      (g.smooth ⊤).iteratedFDeriv_right (by exact_mod_cast le_top)
    have hd : HasFDerivAt ((f:E → ℂ) ⋆[B,μ] iteratedFDeriv ℝ n g)
        (((f:E → ℂ) ⋆[B.precompR E,μ] fderiv ℝ (iteratedFDeriv ℝ n g)) x) x :=
      (hg.iteratedFDeriv n).hasFDerivAt_convolution_right B
        (f.integrable (μ:=μ)).locallyIntegrable hn x
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,he,hd.fderiv]
    let L : (E →L[ℝ] (E [×n]→L[ℝ] ℂ)) →L[ℝ] (E [×(n+1)]→L[ℝ] ℂ) :=
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n+1) => E) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change L (∫ a,(B.precompR E)
      (f a) (fderiv ℝ (iteratedFDeriv ℝ n g) (x-a)) ∂μ)=_
    have hcs : HasCompactSupport (fun a : E => fderiv ℝ (iteratedFDeriv ℝ n g) (x-a)) :=
      ((hg.iteratedFDeriv n).fderiv ℝ).comp_homeomorph (Homeomorph.subLeft x)
    have hci : Continuous (fun a : E => f a • fderiv ℝ (iteratedFDeriv ℝ n g) (x-a)) :=
      f.continuous.smul ((hn.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id))
    have hi : Integrable (fun a : E => f a • fderiv ℝ (iteratedFDeriv ℝ n g) (x-a)) μ := by
      apply hci.integrable_of_hasCompactSupport
      apply hcs.mono
      intro a ha
      simp only [Function.mem_support] at ha ⊢
      intro hz
      exact ha (by rw [hz,smul_zero])
    have hdint : Integrable (fun a =>
        (B.precompR E) (f a)
          (fderiv ℝ (iteratedFDeriv ℝ n g) (x-a))) μ :=
      hi
    have hcomm := L.integral_comp_comm hdint
    rw [← hcomm]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => rfl)

end AASCKleinGordon
