import L2BoundedMultiplication
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AASCKleinGordon.Multiplication
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem L2_norm_sq_integral (f : H μ) : ‖f‖^2=∫ x,‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),L2.inner_def,← integral_re (L2.integrable_inner f f)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change Complex.re (inner ℂ (f x) (f x))=‖f x‖^2
    rw [inner_self_eq_norm_sq_to_K]
    change Complex.re ((‖f x‖ : ℂ)^2)=‖f x‖^2
    rw [← Complex.ofReal_pow,Complex.ofReal_re])

theorem L2_norm_sq_integral_raw (f : H μ) (g : X → ℂ) (hg : f=ᵐ[μ] g) :
    ‖f‖^2=∫ x,‖g x‖^2 ∂μ := by
  rw [L2_norm_sq_integral]
  apply integral_congr_ae
  exact hg.mono (fun x hx => by change ‖f x‖^2=‖g x‖^2; rw [hx])

theorem L2_tendsto_zero_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → H μ) (raw : ι → X → ℂ) (hraw : ∀ t,F t=ᵐ[μ] raw t)
    (hm : ∀ t,AEStronglyMeasurable (raw t) μ)
    (bound : X → ℝ) (hb : MemLp bound 2 μ)
    (hbound : ∀ᶠ t in l,∀ᵐ x ∂μ,‖raw t x‖≤bound x)
    (hlim : ∀ᵐ x ∂μ,Tendsto (fun t => raw t x) l (𝓝 0)) :
    Tendsto F l (𝓝 0) := by
  have ht : Tendsto (fun t => ∫ x,‖raw t x‖^2 ∂μ) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (fun x => bound x^2)
      (Eventually.of_forall (fun t => ((hm t).norm.pow 2)))
      (hbound.mono (fun t ht => ht.mono (fun x hx => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2)))
      hb.integrable_sq
      (hlim.mono (fun x hx => by simpa using hx.norm.pow 2))
    simpa using h
  have he : (fun t => ‖F t‖^2)=(fun t => ∫ x,‖raw t x‖^2 ∂μ) :=
    funext (fun t => L2_norm_sq_integral_raw (F t) (raw t) (hraw t))
  rw [← he] at ht
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hn' : Tendsto (fun t => ‖F t‖) l (𝓝 0) := by
    change Tendsto (fun t => Real.sqrt (‖F t‖^2)) l (𝓝 (Real.sqrt 0)) at hn
    have hs : (fun t => Real.sqrt (‖F t‖^2))=(fun t => ‖F t‖) := by
      funext t
      exact (Real.sqrt_sq_eq_abs _).trans (abs_of_nonneg (norm_nonneg _))
    simpa only [hs,Real.sqrt_zero] using hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'

end AASCKleinGordon.Multiplication
