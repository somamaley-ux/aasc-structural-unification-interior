import KGCoherentVectors
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
set_option maxHeartbeats 2000000
open scoped SchwartzMap ENNReal
namespace AASCKleinGordon

theorem complex_series_zero_forces_coefficients_zero (c : ℕ → ℂ)
    (h : ∀ z : ℂ,HasSum (fun n => c n*z^n) 0) : ∀ n,c n=0 := by
  let p:=FormalMultilinearSeries.ofScalars ℂ c
  have hs : Summable c := by simpa only [one_pow,mul_one] using (h 1).summable
  have hn : Summable (fun n => ‖c n‖):=summable_norm_iff.mpr hs
  have hr : (1 : ℝ≥0∞)≤p.radius := by
    have hr':=(p.le_radius_of_summable (r:=1) (by
      simpa only [p,FormalMultilinearSeries.ofScalars_norm,NNReal.coe_one,one_pow,mul_one] using hn))
    simpa only [ENNReal.coe_one] using hr'
  have hp : HasFPowerSeriesOnBall (0 : ℂ → ℂ) p 0 1 := by
    refine ⟨hr,by norm_num,?_⟩
    intro z _
    simpa only [p,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,Pi.zero_apply] using h z
  have hz : p=0:=hp.hasFPowerSeriesAt.eq_zero
  have hc : c=0:=(FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).mp hz
  exact fun n => congrFun hc n

theorem coherentSector_smul (a : Parameters) (z : ℂ) (f : 𝓢(Momentum,ℂ)) (n : ℕ) :
    coherentSector a (z • f) n=z^n • coherentSector a f n := by
  rw [coherentSector,bosonicTensorPowerHilbert_smul,coherentSector,smul_smul,smul_smul,mul_comm]

/-- Orthogonality to all actual exponential vectors separates every original
bosonic sector and every original diagonal Schwartz tensor power. -/
theorem exponentialVector_orthogonal_separates_sectors (a : Parameters) (v : FockHilbert a)
    (h : ∀ f : 𝓢(Momentum,ℂ),inner ℂ v (exponentialVector a f)=0) :
    ∀ (f : 𝓢(Momentum,ℂ)) (n : ℕ),inner ℂ (v n) (bosonicTensorPowerHilbert a f n)=0 := by
  intro f n
  let c : ℕ → ℂ:=fun k => inner ℂ (v k) (coherentSector a f k)
  have hz (z : ℂ) : HasSum (fun k => c k*z^k) 0 := by
    have hh:=lp.hasSum_inner (𝕜:=ℂ) v (exponentialVector a (z • f))
    rw [h (z • f)] at hh
    simpa only [exponentialVector_component,coherentSector_smul,inner_smul_right,c,mul_comm] using hh
  have hc:=complex_series_zero_forces_coefficients_zero c hz n
  change inner ℂ (v n) (coherentSector a f n)=0 at hc
  rw [coherentSector,inner_smul_right] at hc
  apply (mul_eq_zero.mp hc).resolve_left
  apply inv_ne_zero
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos n)))

end AASCKleinGordon
