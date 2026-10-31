import L2HilbertSumDiagonal
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Filter
open scoped Topology
namespace AASCKleinGordon.HilbertSum
variable {ι κ : Type*} {E : ι → Type*}
  [∀ i,NormedAddCommGroup (E i)] [∀ i,InnerProductSpace ℂ (E i)]

theorem norm_sq_tsum (f : lp E 2) : ‖f‖^2=∑' i,‖f i‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.norm_rpow_eq_tsum (by norm_num) f

theorem tendsto_zero_of_dominated {l : Filter κ} (F : κ → lp E 2) (bound : ι → ℝ)
    (hb : Summable (fun i => bound i^2))
    (hlim : ∀ i,Tendsto (fun t => F t i) l (𝓝 0))
    (hbound : ∀ᶠ t in l,∀ i,‖F t i‖≤bound i) : Tendsto F l (𝓝 0) := by
  have ht := tendsto_tsum_of_dominated_convergence hb
    (fun i => by simpa using (hlim i).norm.pow 2)
    (hbound.mono (fun t ht i => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (ht i) 2))
  have ht' : Tendsto (fun t => ‖F t‖^2) l (𝓝 0) := by
    simpa only [← norm_sq_tsum,tsum_zero] using ht
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  change Tendsto (fun t => Real.sqrt (‖F t‖^2)) l (𝓝 (Real.sqrt 0)) at hn
  have hs : (fun t => Real.sqrt (‖F t‖^2))=(fun t => ‖F t‖) := by
    funext t
    exact (Real.sqrt_sq_eq_abs _).trans (abs_of_nonneg (norm_nonneg _))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [hs,Real.sqrt_zero] using hn

end AASCKleinGordon.HilbertSum
