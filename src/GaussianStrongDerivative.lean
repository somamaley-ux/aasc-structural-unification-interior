import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Filter
open scoped Topology
namespace AASCKleinGordon

/-- A norm identity, rather than an assumed weak or strong derivative, suffices.
The concrete Gaussian Fock family supplies this identity in the next module. -/
theorem hasDerivAt_of_gaussian_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (B : E) (r : ℝ)
    (hrem : ∀ t : ℝ, ‖F t-F 0-t • B‖^2=Real.exp (t^2*r)-1-t^2*r) :
    HasDerivAt F B 0 := by
  let q : ℝ → ℝ := fun t => ‖t‖⁻¹*‖F t-F 0-t • B‖
  have hds : ContinuousAt (dslope Real.exp 0) 0 :=
    continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
  have hlim : Tendsto (fun t : ℝ => r*(dslope Real.exp 0 (t^2*r)-1)) (𝓝 0) (𝓝 0) := by
    have hu : Tendsto (fun t : ℝ => t^2*r) (𝓝 0) (𝓝 0) := by
      simpa using (((continuous_id : Continuous (fun t : ℝ => t)).pow 2).mul continuous_const).tendsto 0
    have hh := (hds.tendsto.comp hu).sub_const 1
    simpa using hh.const_mul r
  have hsq (t : ℝ) : q t ^2=r*(dslope Real.exp 0 (t^2*r)-1) := by
    by_cases ht : t=0
    · subst t
      simp [q,Real.deriv_exp]
    · have he := sub_smul_dslope Real.exp 0 (t^2*r)
      simp only [sub_zero,smul_eq_mul,Real.exp_zero] at he
      dsimp [q]
      rw [mul_pow,hrem,inv_pow,sq_abs]
      field_simp
      nlinarith [he]
  have hq (t : ℝ) : Real.sqrt (r*(dslope Real.exp 0 (t^2*r)-1))=q t := by
    rw [← hsq,Real.sqrt_sq_eq_abs,abs_of_nonneg]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  have hh : Tendsto (fun t : ℝ => Real.sqrt (r*(dslope Real.exp 0 (t^2*r)-1))) (𝓝 0) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hlim
  simp_rw [hq] at hh
  apply hasDerivAt_iff_tendsto.mpr
  simpa only [sub_zero] using hh

end AASCKleinGordon
