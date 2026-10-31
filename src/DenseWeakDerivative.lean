import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory
namespace AASCKleinGordon

theorem hasDerivAt_of_dense_inner_derivative {E D : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (j : D → E) (hd : DenseRange j) (F V : ℝ → E) (hV : Continuous V)
    (hw : ∀ d r,HasDerivAt (fun t => inner ℂ (j d) (F t)) (inner ℂ (j d) (V r)) r)
    (r : ℝ) : HasDerivAt F (V r) r := by
  let G : ℝ → E := fun t => F 0 + ∫ s : ℝ in 0..t,V s
  have hG (t : ℝ) : HasDerivAt G (V t) t := by
    simpa only [G,zero_add] using (hV.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (F 0)
  have he (t : ℝ) : F t = G t := by
    have ht (d : D) : inner ℂ (j d) (F t) = inner ℂ (j d) (G t) := by
      have hg (s : ℝ) : HasDerivAt (fun u => inner ℂ (j d) (G u)) (inner ℂ (j d) (V s)) s :=
        ((innerSL ℂ (j d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hG s)
      have hh (s : ℝ) : HasDerivAt (fun u => inner ℂ (j d) (F u)-inner ℂ (j d) (G u)) 0 s := by
        simpa only [sub_self] using (hw d s).sub (hg s)
      have hc := is_const_of_deriv_eq_zero (fun s => (hh s).differentiableAt)
        (fun s => (hh s).deriv) t 0
      apply sub_eq_zero.mp
      simpa only [G,intervalIntegral.integral_same,add_zero,sub_self] using hc
    have hall := hd.equalizer
      (show Continuous (fun w : E => inner ℂ w (F t)) from continuous_id.inner continuous_const)
      (show Continuous (fun w : E => inner ℂ w (G t)) from continuous_id.inner continuous_const)
      (funext ht)
    exact ext_inner_left ℂ (fun w => congrFun hall w)
  have hfun : F = G := funext he
  rw [hfun]
  exact hG r

end AASCKleinGordon
