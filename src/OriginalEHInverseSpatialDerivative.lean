import OriginalEHBoundaryCurrent

/-! Actual spatial matrix calculus needed in the pending Palatini cancellation.
These are differentiated matrix identities, not assumptions about the response. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

def ehMatrixPartial (M : MetricField) (p : CoordinatePoint) (c : Fin 4) : Tensor2 :=
  fun a b => scalarPartial (fun x => M x a b) p c

theorem eh_matrix_partial_mul (M N : MetricField) (p : CoordinatePoint) (c : Fin 4)
    (hM : ∀ a b, DifferentiableAt ℝ (fun x => M x a b) p)
    (hN : ∀ a b, DifferentiableAt ℝ (fun x => N x a b) p) :
    ehMatrixPartial (fun x => M x * N x) p c =
      ehMatrixPartial M p c * N p + M p * ehMatrixPartial N p c := by
  ext a b
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hM a i).hasFDerivAt.mul (hN i b).hasFDerivAt)
  have hf := hd.fderiv
  change fderiv ℝ (fun x => ∑ i : Fin 4, M x a i * N x i b) p = _ at hf
  simp only [ehMatrixPartial,scalarPartial,Matrix.mul_apply,Matrix.add_apply,hf,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eh_matrix_partial_neg (M : MetricField) (p : CoordinatePoint) (c : Fin 4)
    (hM : ∀ a b, DifferentiableAt ℝ (fun x => M x a b) p) :
    ehMatrixPartial (fun x => -M x) p c = -ehMatrixPartial M p c := by
  ext a b
  have hd := (hM a b).hasFDerivAt.neg.fderiv
  change fderiv ℝ (fun x => -M x a b) p = _ at hd
  simp only [ehMatrixPartial,scalarPartial,Matrix.neg_apply,hd,ContinuousLinearMap.neg_apply]

theorem eh_inverse_spatial_derivative (g : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (c : Fin 4) :
    ehMatrixPartial (fun x => (g x)⁻¹) p c =
      -(g p)⁻¹ * ehMatrixPartial g p c * (g p)⁻¹ := by
  have reg : ∀ a b, ContDiffAt ℝ 2 (fun x => g x a b) p := fun a b =>
    (hg a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have near : (fun x => (g x)⁻¹ * g x) =ᶠ[𝓝 p] fun _ => (1 : Tensor2) :=
    (c2_metric_nondegenerate_eventually g p reg hn).mono (fun x hx =>
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hx))
  have partialZero : ehMatrixPartial (fun x => (g x)⁻¹ * g x) p c = 0 := by
    ext a b
    have he := near.mono (fun x hx => congrArg (fun M : Tensor2 => M a b) hx)
    have hd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) he
    change fderiv ℝ (fun x => ((g x)⁻¹ * g x) a b) p =
      fderiv ℝ (fun _ : CoordinatePoint => (1 : Tensor2) a b) p at hd
    rw [(hasFDerivAt_const (𝕜 := ℝ) ((1 : Tensor2) a b) p).fderiv] at hd
    exact congrArg (fun D : CoordinatePoint →L[ℝ] ℝ => D (Pi.single c 1)) hd
  rw [eh_matrix_partial_mul _ _ p c
    (fun a b => (eh_inverse_component_smooth_at g hg p hn a b).differentiableAt (by norm_num))
    (fun a b => (hg a b).differentiable (by norm_num) p)] at partialZero
  have inverse : g p * (g p)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn)
  have times := congrArg (fun M : Tensor2 => M * (g p)⁻¹) partialZero
  dsimp only at times
  rw [add_mul,mul_assoc,inverse,mul_one,zero_mul] at times
  simpa only [neg_mul] using (eq_neg_of_add_eq_zero_left times)

end
end AASCSemanticExhaustion
