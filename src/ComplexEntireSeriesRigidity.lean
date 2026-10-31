import KGCoherentSectorSeparation
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option maxHeartbeats 1800000
open scoped ENNReal NNReal
namespace AASCKleinGordon

/-- An everywhere convergent genuine scalar power series is entire. -/
theorem complex_series_differentiable (c : ℕ → ℂ) (F : ℂ → ℂ)
    (h : ∀ z : ℂ,HasSum (fun n => c n*z^n) (F z)) : Differentiable ℂ F := by
  intro z
  let p:=FormalMultilinearSeries.ofScalars ℂ c
  let r : ℝ≥0:=‖z‖₊+1
  have hn : Summable (fun n => ‖c n‖*(r : ℝ)^n) := by
    have hs:=summable_norm_iff.mpr (h (r : ℂ)).summable
    simpa only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg r.coe_nonneg] using hs
  have hr : (r : ℝ≥0∞)≤p.radius :=
    p.le_radius_of_summable (by
      simpa only [p,FormalMultilinearSeries.ofScalars_norm] using hn)
  have hp : HasFPowerSeriesOnBall F p 0 r := by
    refine ⟨hr,by exact_mod_cast (show (0 : ℝ≥0)<r from by dsimp [r]; positivity),?_⟩
    intro w _
    simpa only [p,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,zero_add] using h w
  apply (hp.analyticAt_of_mem ?_).differentiableAt
  change edist z 0<(r : ℝ≥0∞)
  rw [edist_zero_right,enorm_eq_nnnorm,ENNReal.coe_lt_coe]
  exact lt_add_one ‖z‖₊

/-- A holomorphic function that is the conjugate of another holomorphic function
is constant. The real derivatives at 1 and i force its complex derivative to vanish. -/
theorem differentiable_eq_conj_forces_constant (A B : ℂ → ℂ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (h : ∀ z,A z=star (B z)) (z w : ℂ) : A z=A w := by
  apply is_const_of_deriv_eq_zero hA _ z w
  intro x
  have ha:=(hA x).hasDerivAt.complexToReal_fderiv
  have hb:=(hB x).hasDerivAt.complexToReal_fderiv
  have hc:=(Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp x hb
  have heq : (fun u => star (B u))=A:=funext (fun u => (h u).symm)
  change HasFDerivAt (fun u => star (B u)) _ x at hc
  rw [heq] at hc
  have hd:=ha.unique hc
  have h1:=congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hd
  have hi:=congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) hd
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,
    smul_eq_mul,mul_one,ContinuousLinearMap.comp_apply] at h1 hi
  change deriv A x=starRingEnd ℂ (deriv B x) at h1
  change deriv A x*Complex.I=starRingEnd ℂ (deriv B x*Complex.I) at hi
  rw [map_mul,Complex.conj_I,← h1] at hi
  have hi' : (deriv A x)*(2*Complex.I)=0 := by
    linear_combination hi
  exact (mul_eq_zero.mp hi').resolve_right (by norm_num [Complex.I_ne_zero])

end AASCKleinGordon
