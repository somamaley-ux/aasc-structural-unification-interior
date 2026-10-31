import KGOriginalLocalWickAssembly

noncomputable section
set_option maxHeartbeats 4000000
namespace AASCKleinGordon

theorem wick_finite_weighted_directional_derivative {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (F : ι → Spacetime → ℂ) (x d : Spacetime)
    (hf : ∀ i∈S,DifferentiableAt ℝ (F i) x) :
    fderiv ℝ (fun x => ∑ i∈S,c i * F i x) x d =
      ∑ i∈S,c i * fderiv ℝ (F i) x d := by
  rw [fderiv_fun_sum (fun i hi => (hf i hi).const_mul (c i))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_const_mul (hf i hi) (c i), ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem wick_scaled_finite_weighted_directional_derivative {ι : Type*} (S : Finset ι)
    (b : ℂ) (c : ι → ℂ) (F : ι → Spacetime → ℂ) (x d : Spacetime)
    (hf : ∀ i∈S,DifferentiableAt ℝ (F i) x) :
    fderiv ℝ (fun x => b * ∑ i∈S,c i * F i x) x d =
      b * ∑ i∈S,c i * fderiv ℝ (F i) x d := by
  have hs : DifferentiableAt ℝ (fun x => ∑ i∈S,c i * F i x) x :=
    DifferentiableAt.fun_sum (fun i hi => (hf i hi).const_mul (c i))
  rw [fderiv_const_mul hs b, ContinuousLinearMap.smul_apply, smul_eq_mul,
    wick_finite_weighted_directional_derivative S c F x d hf]

end AASCKleinGordon
