import OriginalEHInverseSpatialDerivative

/-! Differentiate the already computed inverse-metric variation spatially.
The resulting mixed-variation polynomial is proved from matrix calculus. -/
namespace AASCSemanticExhaustion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Topology ContDiff BigOperators Matrix.Norms.Elementwise

theorem eh_matrix_mul_components_differentiableAt (M N : MetricField) (p : CoordinatePoint)
    (hM : ∀ a b, DifferentiableAt ℝ (fun x => M x a b) p)
    (hN : ∀ a b, DifferentiableAt ℝ (fun x => N x a b) p) :
    ∀ a b, DifferentiableAt ℝ (fun x => (M x * N x) a b) p := by
  intro a b
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hM a i).hasFDerivAt.mul (hN i b).hasFDerivAt)
  simpa only [Matrix.mul_apply,Pi.mul_apply] using hd.differentiableAt

theorem eh_inverse_variation_spatial_derivative (g h : MetricField)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun x => g x a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun x => h x a b)) (p : CoordinatePoint)
    (hn : (g p).det ≠ 0) (c : Fin 4) :
    ehMatrixPartial (fun x => ehInverseVariation g h x) p c =
      (g p)⁻¹ * ehMatrixPartial g p c * (g p)⁻¹ * h p * (g p)⁻¹ -
        (g p)⁻¹ * ehMatrixPartial h p c * (g p)⁻¹ +
        (g p)⁻¹ * h p * (g p)⁻¹ * ehMatrixPartial g p c * (g p)⁻¹ := by
  let B : MetricField := fun x => (g x)⁻¹
  have hb : ∀ a b, DifferentiableAt ℝ (fun x => B x a b) p := fun a b =>
    (eh_inverse_component_smooth_at g hg p hn a b).differentiableAt (by norm_num)
  have hh' : ∀ a b, DifferentiableAt ℝ (fun x => h x a b) p := fun a b =>
    (hh a b).differentiable (by norm_num) p
  have hbh := eh_matrix_mul_components_differentiableAt B h p hb hh'
  have hbhb := eh_matrix_mul_components_differentiableAt (fun x => B x * h x) B p hbh hb
  have same : (fun x => ehInverseVariation g h x) = fun x => -(B x * h x * B x) := by
    funext x
    simp only [ehInverseVariation,B,neg_mul]
  rw [same,eh_matrix_partial_neg _ p c hbhb,
    eh_matrix_partial_mul _ B p c hbh hb,eh_matrix_partial_mul B h p c hb hh']
  have hi : ehMatrixPartial B p c = -B p * ehMatrixPartial g p c * B p :=
    eh_inverse_spatial_derivative g hg p hn c
  rw [hi]
  dsimp only [B]
  noncomm_ring

end
end AASCSemanticExhaustion
